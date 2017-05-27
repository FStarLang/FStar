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
          (uu____1747,uu____1748,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___108_1777  ->
                  match uu___108_1777 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1778 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1779,uu____1780,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
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
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1838 uu____1840 None
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
              if uu____1931 then tok_of_name env f else None
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
              if uu____1947 then Some t else None
          | uu____1952 -> None in
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
    | FStar_Const.Const_int (i,None ) ->
        let uu____2056 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2056
    | FStar_Const.Const_int (i,Some uu____2058) ->
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
    (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)
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
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Syntax_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2167::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2169 -> false
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
        (let uu____2314 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2314
         then
           let uu____2315 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2315
         else ());
        (let uu____2317 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2353  ->
                   fun b  ->
                     match uu____2353 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2396 =
                           let x = unmangle (fst b) in
                           let uu____2405 = gen_term_var env1 x in
                           match uu____2405 with
                           | (xxsym,xx,env') ->
                               let uu____2419 =
                                 let uu____2422 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2422 env1 xx in
                               (match uu____2419 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2396 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2317 with
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
          let uu____2510 = encode_term t env in
          match uu____2510 with
          | (t1,decls) ->
              let uu____2517 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2517, decls)
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
          let uu____2525 = encode_term t env in
          match uu____2525 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2534 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2534, decls)
               | Some f ->
                   let uu____2536 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2536, decls))
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
        let uu____2542 = encode_args args_e env in
        match uu____2542 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2554 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____2561 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____2561 in
            let binary arg_tms1 =
              let uu____2570 =
                let uu____2571 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____2571 in
              let uu____2572 =
                let uu____2573 =
                  let uu____2574 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2574 in
                FStar_SMTEncoding_Term.unboxInt uu____2573 in
              (uu____2570, uu____2572) in
            let mk_default uu____2579 =
              let uu____2580 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2580 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____2625 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2625
              then
                let uu____2626 = let uu____2627 = mk_args ts in op uu____2627 in
                FStar_All.pipe_right uu____2626 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____2650 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____2650
              then
                let uu____2651 = binary ts in
                match uu____2651 with
                | (t1,t2) ->
                    let uu____2656 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____2656
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2659 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____2659
                 then
                   let uu____2660 = op (binary ts) in
                   FStar_All.pipe_right uu____2660
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
            let uu____2750 =
              let uu____2756 =
                FStar_List.tryFind
                  (fun uu____2768  ->
                     match uu____2768 with
                     | (l,uu____2775) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____2756 FStar_Util.must in
            (match uu____2750 with
             | (uu____2800,op) ->
                 let uu____2808 = op arg_tms in (uu____2808, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2815 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2815
       then
         let uu____2816 = FStar_Syntax_Print.tag_of_term t in
         let uu____2817 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2818 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2816 uu____2817
           uu____2818
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2822 ->
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
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2850 =
             let uu____2851 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2852 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2853 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2854 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2851
               uu____2852 uu____2853 uu____2854 in
           failwith uu____2850
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2858 =
             let uu____2859 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2859 in
           failwith uu____2858
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2864) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2894) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2903 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2903, [])
       | FStar_Syntax_Syntax.Tm_type uu____2909 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2912) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2918 = encode_const c in (uu____2918, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2933 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2933 with
            | (binders1,res) ->
                let uu____2940 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2940
                then
                  let uu____2943 = encode_binders None binders1 env in
                  (match uu____2943 with
                   | (vars,guards,env',decls,uu____2958) ->
                       let fsym =
                         let uu____2968 = varops.fresh "f" in
                         (uu____2968, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2971 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_2975 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_2975.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_2975.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_2975.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_2975.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_2975.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_2975.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_2975.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_2975.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_2975.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_2975.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_2975.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_2975.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_2975.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_2975.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_2975.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_2975.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_2975.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_2975.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_2975.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_2975.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_2975.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_2975.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_2975.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2971 with
                        | (pre_opt,res_t) ->
                            let uu____2982 =
                              encode_term_pred None res_t env' app in
                            (match uu____2982 with
                             | (res_pred,decls') ->
                                 let uu____2989 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2996 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2996, [])
                                   | Some pre ->
                                       let uu____2999 =
                                         encode_formula pre env' in
                                       (match uu____2999 with
                                        | (guard,decls0) ->
                                            let uu____3007 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3007, decls0)) in
                                 (match uu____2989 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3015 =
                                          let uu____3021 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3021) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3015 in
                                      let cvars =
                                        let uu____3031 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3031
                                          (FStar_List.filter
                                             (fun uu____3037  ->
                                                match uu____3037 with
                                                | (x,uu____3041) ->
                                                    x <> (fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3052 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3052 with
                                       | Some cache_entry ->
                                           let uu____3057 =
                                             let uu____3058 =
                                               let uu____3062 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3062) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3058 in
                                           (uu____3057,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____3073 =
                                               let uu____3074 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3074 in
                                             varops.mk_unique uu____3073 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars in
                                           let caption =
                                             let uu____3081 =
                                               FStar_Options.log_queries () in
                                             if uu____3081
                                             then
                                               let uu____3083 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____3083
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3089 =
                                               let uu____3093 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3093) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3089 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3101 =
                                               let uu____3105 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3105, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3101 in
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
                                             let uu____3118 =
                                               let uu____3122 =
                                                 let uu____3123 =
                                                   let uu____3129 =
                                                     let uu____3130 =
                                                       let uu____3133 =
                                                         let uu____3134 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3134 in
                                                       (f_has_t, uu____3133) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3130 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3129) in
                                                 mkForall_fuel uu____3123 in
                                               (uu____3122,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3118 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3147 =
                                               let uu____3151 =
                                                 let uu____3152 =
                                                   let uu____3158 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3158) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3152 in
                                               (uu____3151, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3147 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3172 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3172);
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
                     let uu____3183 =
                       let uu____3187 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3187, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3183 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3196 =
                       let uu____3200 =
                         let uu____3201 =
                           let uu____3207 =
                             let uu____3208 =
                               let uu____3211 =
                                 let uu____3212 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3212 in
                               (f_has_t, uu____3211) in
                             FStar_SMTEncoding_Util.mkImp uu____3208 in
                           ([[f_has_t]], [fsym], uu____3207) in
                         mkForall_fuel uu____3201 in
                       (uu____3200, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3196 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3226 ->
           let uu____3231 =
             let uu____3234 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3234 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3239;
                 FStar_Syntax_Syntax.pos = uu____3240;
                 FStar_Syntax_Syntax.vars = uu____3241;_} ->
                 let uu____3248 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____3248 with
                  | (b,f1) ->
                      let uu____3262 =
                        let uu____3263 = FStar_List.hd b in fst uu____3263 in
                      (uu____3262, f1))
             | uu____3268 -> failwith "impossible" in
           (match uu____3231 with
            | (x,f) ->
                let uu____3275 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3275 with
                 | (base_t,decls) ->
                     let uu____3282 = gen_term_var env x in
                     (match uu____3282 with
                      | (x1,xtm,env') ->
                          let uu____3291 = encode_formula f env' in
                          (match uu____3291 with
                           | (refinement,decls') ->
                               let uu____3298 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3298 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3309 =
                                        let uu____3311 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3315 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3311
                                          uu____3315 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3309 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3331  ->
                                              match uu____3331 with
                                              | (y,uu____3335) ->
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
                                    let uu____3354 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3354 with
                                     | Some cache_entry ->
                                         let uu____3359 =
                                           let uu____3360 =
                                             let uu____3364 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3364) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3360 in
                                         (uu____3359,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3376 =
                                             let uu____3377 =
                                               let uu____3378 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3378 in
                                             Prims.strcat module_name
                                               uu____3377 in
                                           varops.mk_unique uu____3376 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3387 =
                                             let uu____3391 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3391) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3387 in
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
                                           let uu____3401 =
                                             let uu____3405 =
                                               let uu____3406 =
                                                 let uu____3412 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3412) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3406 in
                                             (uu____3405,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3401 in
                                         let t_kinding =
                                           let uu____3422 =
                                             let uu____3426 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3426,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3422 in
                                         let t_interp =
                                           let uu____3436 =
                                             let uu____3440 =
                                               let uu____3441 =
                                                 let uu____3447 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3447) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3441 in
                                             let uu____3459 =
                                               let uu____3461 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3461 in
                                             (uu____3440, uu____3459,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3436 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3466 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3466);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3483 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3483 in
           let uu____3487 = encode_term_pred None k env ttm in
           (match uu____3487 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3495 =
                    let uu____3499 =
                      let uu____3500 =
                        let uu____3501 =
                          let uu____3502 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3502 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3501 in
                      varops.mk_unique uu____3500 in
                    (t_has_k, (Some "Uvar typing"), uu____3499) in
                  FStar_SMTEncoding_Util.mkAssume uu____3495 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3508 ->
           let uu____3518 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3518 with
            | (head1,args_e) ->
                let uu____3546 =
                  let uu____3554 =
                    let uu____3555 = FStar_Syntax_Subst.compress head1 in
                    uu____3555.FStar_Syntax_Syntax.n in
                  (uu____3554, args_e) in
                (match uu____3546 with
                 | uu____3565 when head_redex env head1 ->
                     let uu____3573 = whnf env t in
                     encode_term uu____3573 env
                 | uu____3574 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____3587;
                       FStar_Syntax_Syntax.pos = uu____3588;
                       FStar_Syntax_Syntax.vars = uu____3589;_},uu____3590),uu____3591::
                    (v1,uu____3593)::(v2,uu____3595)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3633 = encode_term v1 env in
                     (match uu____3633 with
                      | (v11,decls1) ->
                          let uu____3640 = encode_term v2 env in
                          (match uu____3640 with
                           | (v21,decls2) ->
                               let uu____3647 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3647,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3650::(v1,uu____3652)::(v2,uu____3654)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3688 = encode_term v1 env in
                     (match uu____3688 with
                      | (v11,decls1) ->
                          let uu____3695 = encode_term v2 env in
                          (match uu____3695 with
                           | (v21,decls2) ->
                               let uu____3702 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3702,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3704) ->
                     let e0 =
                       let uu____3716 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3716 in
                     ((let uu____3722 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3722
                       then
                         let uu____3723 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3723
                       else ());
                      (let e =
                         let uu____3728 =
                           let uu____3729 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3730 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3729
                             uu____3730 in
                         uu____3728 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3739),(arg,uu____3741)::[]) -> encode_term arg env
                 | uu____3759 ->
                     let uu____3767 = encode_args args_e env in
                     (match uu____3767 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3800 = encode_term head1 env in
                            match uu____3800 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3839 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3839 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3881  ->
                                                 fun uu____3882  ->
                                                   match (uu____3881,
                                                           uu____3882)
                                                   with
                                                   | ((bv,uu____3896),
                                                      (a,uu____3898)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3912 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3912
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3917 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3917 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3927 =
                                                   let uu____3931 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3936 =
                                                     let uu____3937 =
                                                       let uu____3938 =
                                                         let uu____3939 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3939 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3938 in
                                                     varops.mk_unique
                                                       uu____3937 in
                                                   (uu____3931,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3936) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3927 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3956 = lookup_free_var_sym env fv in
                            match uu____3956 with
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
                                   FStar_Syntax_Syntax.tk = uu____3979;
                                   FStar_Syntax_Syntax.pos = uu____3980;
                                   FStar_Syntax_Syntax.vars = uu____3981;_},uu____3982)
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____3993;
                                   FStar_Syntax_Syntax.pos = uu____3994;
                                   FStar_Syntax_Syntax.vars = uu____3995;_},uu____3996)
                                ->
                                let uu____4001 =
                                  let uu____4002 =
                                    let uu____4005 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4005
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4002
                                    FStar_Pervasives.snd in
                                Some uu____4001
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4025 =
                                  let uu____4026 =
                                    let uu____4029 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4029
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4026
                                    FStar_Pervasives.snd in
                                Some uu____4025
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4048,(FStar_Util.Inl t1,uu____4050),uu____4051)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4089,(FStar_Util.Inr c,uu____4091),uu____4092)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4130 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4150 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4150 in
                               let uu____4151 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4151 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4161;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4162;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4163;_},uu____4164)
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
                                     | uu____4188 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4233 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4233 with
            | (bs1,body1,opening) ->
                let fallback uu____4248 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____4253 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4253, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4264 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____4264
                  | FStar_Util.Inr (eff,uu____4266) ->
                      let uu____4272 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____4272 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4317 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___136_4318 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___136_4318.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___136_4318.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___136_4318.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___136_4318.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___136_4318.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___136_4318.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___136_4318.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___136_4318.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___136_4318.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___136_4318.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___136_4318.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___136_4318.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___136_4318.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___136_4318.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___136_4318.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___136_4318.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___136_4318.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___136_4318.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___136_4318.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___136_4318.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___136_4318.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___136_4318.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___136_4318.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4317 FStar_Syntax_Syntax.U_unknown in
                        let uu____4319 =
                          let uu____4320 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4320 in
                        FStar_Util.Inl uu____4319
                    | FStar_Util.Inr (eff_name,uu____4327) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4358 =
                        let uu____4359 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4359 in
                      FStar_All.pipe_right uu____4358
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4371 =
                        let uu____4372 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4372 FStar_Pervasives.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4380 =
                          let uu____4381 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4381 in
                        FStar_All.pipe_right uu____4380
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4385 =
                             let uu____4386 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4386 in
                           FStar_All.pipe_right uu____4385
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4397 =
                         let uu____4398 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4398 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4397);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4413 =
                       (is_impure lc1) &&
                         (let uu____4414 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4414) in
                     if uu____4413
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4419 = encode_binders None bs1 env in
                        match uu____4419 with
                        | (vars,guards,envbody,decls,uu____4434) ->
                            let uu____4441 =
                              let uu____4449 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4449
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4441 with
                             | (lc2,body2) ->
                                 let uu____4474 = encode_term body2 envbody in
                                 (match uu____4474 with
                                  | (body3,decls') ->
                                      let uu____4481 =
                                        let uu____4486 = codomain_eff lc2 in
                                        match uu____4486 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4498 =
                                              encode_term tfun env in
                                            (match uu____4498 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4481 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4517 =
                                               let uu____4523 =
                                                 let uu____4524 =
                                                   let uu____4527 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4527, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4524 in
                                               ([], vars, uu____4523) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4517 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4535 =
                                                   let uu____4537 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4537 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4535 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4548 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4548 with
                                            | Some cache_entry ->
                                                let uu____4553 =
                                                  let uu____4554 =
                                                    let uu____4558 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4558) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4554 in
                                                (uu____4553,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | None  ->
                                                let uu____4564 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4564 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4571 =
                                                         let uu____4572 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4572 =
                                                           cache_size in
                                                       if uu____4571
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
                                                         let uu____4583 =
                                                           let uu____4584 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4584 in
                                                         varops.mk_unique
                                                           uu____4583 in
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
                                                       let uu____4589 =
                                                         let uu____4593 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4593) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4589 in
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
                                                           let uu____4605 =
                                                             let uu____4606 =
                                                               let uu____4610
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4610,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4606 in
                                                           [uu____4605] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4618 =
                                                         let uu____4622 =
                                                           let uu____4623 =
                                                             let uu____4629 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4629) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4623 in
                                                         (uu____4622,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4618 in
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
                                                     ((let uu____4639 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4639);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4641,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4642;
                          FStar_Syntax_Syntax.lbunivs = uu____4643;
                          FStar_Syntax_Syntax.lbtyp = uu____4644;
                          FStar_Syntax_Syntax.lbeff = uu____4645;
                          FStar_Syntax_Syntax.lbdef = uu____4646;_}::uu____4647),uu____4648)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4666;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4668;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4684 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4697 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4697, [decl_e])))
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
              let uu____4739 = encode_term e1 env in
              match uu____4739 with
              | (ee1,decls1) ->
                  let uu____4746 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4746 with
                   | (xs,e21) ->
                       let uu____4760 = FStar_List.hd xs in
                       (match uu____4760 with
                        | (x1,uu____4768) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4770 = encode_body e21 env' in
                            (match uu____4770 with
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
            let uu____4792 =
              let uu____4796 =
                let uu____4797 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4797 in
              gen_term_var env uu____4796 in
            match uu____4792 with
            | (scrsym,scr',env1) ->
                let uu____4807 = encode_term e env1 in
                (match uu____4807 with
                 | (scr,decls) ->
                     let uu____4814 =
                       let encode_branch b uu____4830 =
                         match uu____4830 with
                         | (else_case,decls1) ->
                             let uu____4841 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4841 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4871  ->
                                       fun uu____4872  ->
                                         match (uu____4871, uu____4872) with
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
                                                       fun uu____4909  ->
                                                         match uu____4909
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4914 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4929 =
                                                     encode_term w1 env2 in
                                                   (match uu____4929 with
                                                    | (w2,decls21) ->
                                                        let uu____4937 =
                                                          let uu____4938 =
                                                            let uu____4941 =
                                                              let uu____4942
                                                                =
                                                                let uu____4945
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4945) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4942 in
                                                            (guard,
                                                              uu____4941) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4938 in
                                                        (uu____4937, decls21)) in
                                             (match uu____4914 with
                                              | (guard1,decls21) ->
                                                  let uu____4953 =
                                                    encode_br br env2 in
                                                  (match uu____4953 with
                                                   | (br1,decls3) ->
                                                       let uu____4961 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4961,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4814 with
                      | (match_tm,decls1) ->
                          let uu____4973 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4973, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____5004 -> let uu____5005 = encode_one_pat env pat in [uu____5005]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____5017 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5017
       then
         let uu____5018 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5018
       else ());
      (let uu____5020 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5020 with
       | (vars,pat_term) ->
           let uu____5030 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5053  ->
                     fun v1  ->
                       match uu____5053 with
                       | (env1,vars1) ->
                           let uu____5081 = gen_term_var env1 v1 in
                           (match uu____5081 with
                            | (xx,uu____5093,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____5030 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____5140 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var uu____5144 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5145 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5146 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5152 =
                        let uu____5155 = encode_const c in
                        (scrutinee, uu____5155) in
                      FStar_SMTEncoding_Util.mkEq uu____5152
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5174 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5174 with
                        | (uu____5178,uu____5179::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5181 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5202  ->
                                  match uu____5202 with
                                  | (arg,uu____5208) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5218 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5218)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____5237 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5245) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5264 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5279 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5301  ->
                                  match uu____5301 with
                                  | (arg,uu____5310) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5320 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5320)) in
                      FStar_All.pipe_right uu____5279 FStar_List.flatten in
                let pat_term1 uu____5336 = encode_term pat_term env1 in
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
      let uu____5343 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5358  ->
                fun uu____5359  ->
                  match (uu____5358, uu____5359) with
                  | ((tms,decls),(t,uu____5379)) ->
                      let uu____5390 = encode_term t env in
                      (match uu____5390 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5343 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5424 = FStar_Syntax_Util.list_elements e in
        match uu____5424 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5442 =
          let uu____5452 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5452 FStar_Syntax_Util.head_and_args in
        match uu____5442 with
        | (head1,args) ->
            let uu____5483 =
              let uu____5491 =
                let uu____5492 = FStar_Syntax_Util.un_uinst head1 in
                uu____5492.FStar_Syntax_Syntax.n in
              (uu____5491, args) in
            (match uu____5483 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5506,uu____5507)::(e,uu____5509)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> (e, None)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5540)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpatT_lid
                 -> (e, None)
             | uu____5561 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or t1 =
          let uu____5594 =
            let uu____5604 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5604 FStar_Syntax_Util.head_and_args in
          match uu____5594 with
          | (head1,args) ->
              let uu____5633 =
                let uu____5641 =
                  let uu____5642 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5642.FStar_Syntax_Syntax.n in
                (uu____5641, args) in
              (match uu____5633 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5655)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5675 -> None) in
        match elts with
        | t1::[] ->
            let uu____5693 = smt_pat_or t1 in
            (match uu____5693 with
             | Some e ->
                 let uu____5709 = list_elements1 e in
                 FStar_All.pipe_right uu____5709
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5726 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5726
                           (FStar_List.map one_pat)))
             | uu____5740 ->
                 let uu____5744 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5744])
        | uu____5775 ->
            let uu____5777 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5777] in
      let uu____5808 =
        let uu____5824 =
          let uu____5825 = FStar_Syntax_Subst.compress t in
          uu____5825.FStar_Syntax_Syntax.n in
        match uu____5824 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5855 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5855 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5890;
                        FStar_Syntax_Syntax.effect_name = uu____5891;
                        FStar_Syntax_Syntax.result_typ = uu____5892;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5894)::(post,uu____5896)::(pats,uu____5898)::[];
                        FStar_Syntax_Syntax.flags = uu____5899;_}
                      ->
                      let uu____5931 = lemma_pats pats in
                      (binders1, pre, post, uu____5931)
                  | uu____5950 -> failwith "impos"))
        | uu____5966 -> failwith "Impos" in
      match uu____5808 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___137_6011 = env in
            {
              bindings = (uu___137_6011.bindings);
              depth = (uu___137_6011.depth);
              tcenv = (uu___137_6011.tcenv);
              warn = (uu___137_6011.warn);
              cache = (uu___137_6011.cache);
              nolabels = (uu___137_6011.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___137_6011.encode_non_total_function_typ);
              current_module_name = (uu___137_6011.current_module_name)
            } in
          let uu____6012 = encode_binders None binders env1 in
          (match uu____6012 with
           | (vars,guards,env2,decls,uu____6027) ->
               let uu____6034 =
                 let uu____6041 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____6072 =
                             let uu____6077 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun uu____6093  ->
                                       match uu____6093 with
                                       | (t1,uu____6100) ->
                                           encode_term t1 env2)) in
                             FStar_All.pipe_right uu____6077 FStar_List.unzip in
                           match uu____6072 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____6041 FStar_List.unzip in
               (match uu____6034 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___138_6150 = env2 in
                      {
                        bindings = (uu___138_6150.bindings);
                        depth = (uu___138_6150.depth);
                        tcenv = (uu___138_6150.tcenv);
                        warn = (uu___138_6150.warn);
                        cache = (uu___138_6150.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___138_6150.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___138_6150.encode_non_total_function_typ);
                        current_module_name =
                          (uu___138_6150.current_module_name)
                      } in
                    let uu____6151 =
                      let uu____6154 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6154 env3 in
                    (match uu____6151 with
                     | (pre1,decls'') ->
                         let uu____6159 =
                           let uu____6162 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6162 env3 in
                         (match uu____6159 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6169 =
                                let uu____6170 =
                                  let uu____6176 =
                                    let uu____6177 =
                                      let uu____6180 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6180, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6177 in
                                  (pats, vars, uu____6176) in
                                FStar_SMTEncoding_Util.mkForall uu____6170 in
                              (uu____6169, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6193 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6193
        then
          let uu____6194 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6195 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6194 uu____6195
        else () in
      let enc f r l =
        let uu____6222 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6235 = encode_term (fst x) env in
                 match uu____6235 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6222 with
        | (decls,args) ->
            let uu____6252 =
              let uu___139_6253 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6253.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6253.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6252, decls) in
      let const_op f r uu____6272 = let uu____6275 = f r in (uu____6275, []) in
      let un_op f l =
        let uu____6291 = FStar_List.hd l in FStar_All.pipe_left f uu____6291 in
      let bin_op f uu___111_6304 =
        match uu___111_6304 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6312 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6339 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6348  ->
                 match uu____6348 with
                 | (t,uu____6356) ->
                     let uu____6357 = encode_formula t env in
                     (match uu____6357 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6339 with
        | (decls,phis) ->
            let uu____6374 =
              let uu___140_6375 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_6375.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_6375.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6374, decls) in
      let eq_op r uu___112_6391 =
        match uu___112_6391 with
        | uu____6394::e1::e2::[] ->
            let uu____6425 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6425 r [e1; e2]
        | uu____6444::uu____6445::e1::e2::[] ->
            let uu____6484 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6484 r [e1; e2]
        | l ->
            let uu____6504 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6504 r l in
      let mk_imp1 r uu___113_6523 =
        match uu___113_6523 with
        | (lhs,uu____6527)::(rhs,uu____6529)::[] ->
            let uu____6550 = encode_formula rhs env in
            (match uu____6550 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6559) ->
                      (l1, decls1)
                  | uu____6562 ->
                      let uu____6563 = encode_formula lhs env in
                      (match uu____6563 with
                       | (l2,decls2) ->
                           let uu____6570 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6570, (FStar_List.append decls1 decls2)))))
        | uu____6572 -> failwith "impossible" in
      let mk_ite r uu___114_6587 =
        match uu___114_6587 with
        | (guard,uu____6591)::(_then,uu____6593)::(_else,uu____6595)::[] ->
            let uu____6624 = encode_formula guard env in
            (match uu____6624 with
             | (g,decls1) ->
                 let uu____6631 = encode_formula _then env in
                 (match uu____6631 with
                  | (t,decls2) ->
                      let uu____6638 = encode_formula _else env in
                      (match uu____6638 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6647 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6666 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6666 in
      let connectives =
        let uu____6678 =
          let uu____6687 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6687) in
        let uu____6700 =
          let uu____6710 =
            let uu____6719 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6719) in
          let uu____6732 =
            let uu____6742 =
              let uu____6752 =
                let uu____6761 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6761) in
              let uu____6774 =
                let uu____6784 =
                  let uu____6794 =
                    let uu____6803 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6803) in
                  [uu____6794;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6784 in
              uu____6752 :: uu____6774 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6742 in
          uu____6710 :: uu____6732 in
        uu____6678 :: uu____6700 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6965 = encode_formula phi' env in
            (match uu____6965 with
             | (phi2,decls) ->
                 let uu____6972 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6972, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6973 ->
            let uu____6978 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6978 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____7007 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____7007 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____7015;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____7017;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____7033 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____7033 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____7065::(x,uu____7067)::(t,uu____7069)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____7103 = encode_term x env in
                 (match uu____7103 with
                  | (x1,decls) ->
                      let uu____7110 = encode_term t env in
                      (match uu____7110 with
                       | (t1,decls') ->
                           let uu____7117 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____7117, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____7121)::(msg,uu____7123)::(phi2,uu____7125)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____7159 =
                   let uu____7162 =
                     let uu____7163 = FStar_Syntax_Subst.compress r in
                     uu____7163.FStar_Syntax_Syntax.n in
                   let uu____7166 =
                     let uu____7167 = FStar_Syntax_Subst.compress msg in
                     uu____7167.FStar_Syntax_Syntax.n in
                   (uu____7162, uu____7166) in
                 (match uu____7159 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7174))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____7190 -> fallback phi2)
             | uu____7193 when head_redex env head2 ->
                 let uu____7201 = whnf env phi1 in
                 encode_formula uu____7201 env
             | uu____7202 ->
                 let uu____7210 = encode_term phi1 env in
                 (match uu____7210 with
                  | (tt,decls) ->
                      let uu____7217 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___141_7218 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___141_7218.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___141_7218.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7217, decls)))
        | uu____7221 ->
            let uu____7222 = encode_term phi1 env in
            (match uu____7222 with
             | (tt,decls) ->
                 let uu____7229 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___142_7230 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___142_7230.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___142_7230.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7229, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7257 = encode_binders None bs env1 in
        match uu____7257 with
        | (vars,guards,env2,decls,uu____7279) ->
            let uu____7286 =
              let uu____7293 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7316 =
                          let uu____7321 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7335  ->
                                    match uu____7335 with
                                    | (t,uu____7341) ->
                                        encode_term t
                                          (let uu___143_7342 = env2 in
                                           {
                                             bindings =
                                               (uu___143_7342.bindings);
                                             depth = (uu___143_7342.depth);
                                             tcenv = (uu___143_7342.tcenv);
                                             warn = (uu___143_7342.warn);
                                             cache = (uu___143_7342.cache);
                                             nolabels =
                                               (uu___143_7342.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___143_7342.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___143_7342.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7321 FStar_List.unzip in
                        match uu____7316 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7293 FStar_List.unzip in
            (match uu____7286 with
             | (pats,decls') ->
                 let uu____7394 = encode_formula body env2 in
                 (match uu____7394 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7413;
                             FStar_SMTEncoding_Term.rng = uu____7414;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7422 -> guards in
                      let uu____7425 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7425, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7459  ->
                   match uu____7459 with
                   | (x,uu____7463) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7469 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7475 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7475) uu____7469 tl1 in
             let uu____7477 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7489  ->
                       match uu____7489 with
                       | (b,uu____7493) ->
                           let uu____7494 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7494)) in
             (match uu____7477 with
              | None  -> ()
              | Some (x,uu____7498) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7508 =
                    let uu____7509 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7509 in
                  FStar_Errors.warn pos uu____7508) in
       let uu____7510 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7510 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7516 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7552  ->
                     match uu____7552 with
                     | (l,uu____7562) -> FStar_Ident.lid_equals op l)) in
           (match uu____7516 with
            | None  -> fallback phi1
            | Some (uu____7585,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7614 = encode_q_body env vars pats body in
             match uu____7614 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7640 =
                     let uu____7646 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7646) in
                   FStar_SMTEncoding_Term.mkForall uu____7640
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7658 = encode_q_body env vars pats body in
             match uu____7658 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7683 =
                   let uu____7684 =
                     let uu____7690 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7690) in
                   FStar_SMTEncoding_Term.mkExists uu____7684
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7683, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7739 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7739 with
  | (asym,a) ->
      let uu____7744 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7744 with
       | (xsym,x) ->
           let uu____7749 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7749 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7779 =
                      let uu____7785 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____7785, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7779 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7800 =
                      let uu____7804 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7804) in
                    FStar_SMTEncoding_Util.mkApp uu____7800 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7812 =
                    let uu____7814 =
                      let uu____7816 =
                        let uu____7818 =
                          let uu____7819 =
                            let uu____7823 =
                              let uu____7824 =
                                let uu____7830 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7830) in
                              FStar_SMTEncoding_Util.mkForall uu____7824 in
                            (uu____7823, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7819 in
                        let uu____7839 =
                          let uu____7841 =
                            let uu____7842 =
                              let uu____7846 =
                                let uu____7847 =
                                  let uu____7853 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7853) in
                                FStar_SMTEncoding_Util.mkForall uu____7847 in
                              (uu____7846,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7842 in
                          [uu____7841] in
                        uu____7818 :: uu____7839 in
                      xtok_decl :: uu____7816 in
                    xname_decl :: uu____7814 in
                  (xtok1, uu____7812) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7902 =
                    let uu____7910 =
                      let uu____7916 =
                        let uu____7917 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7917 in
                      quant axy uu____7916 in
                    (FStar_Syntax_Const.op_Eq, uu____7910) in
                  let uu____7923 =
                    let uu____7932 =
                      let uu____7940 =
                        let uu____7946 =
                          let uu____7947 =
                            let uu____7948 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7948 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7947 in
                        quant axy uu____7946 in
                      (FStar_Syntax_Const.op_notEq, uu____7940) in
                    let uu____7954 =
                      let uu____7963 =
                        let uu____7971 =
                          let uu____7977 =
                            let uu____7978 =
                              let uu____7979 =
                                let uu____7982 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7983 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7982, uu____7983) in
                              FStar_SMTEncoding_Util.mkLT uu____7979 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7978 in
                          quant xy uu____7977 in
                        (FStar_Syntax_Const.op_LT, uu____7971) in
                      let uu____7989 =
                        let uu____7998 =
                          let uu____8006 =
                            let uu____8012 =
                              let uu____8013 =
                                let uu____8014 =
                                  let uu____8017 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____8018 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____8017, uu____8018) in
                                FStar_SMTEncoding_Util.mkLTE uu____8014 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____8013 in
                            quant xy uu____8012 in
                          (FStar_Syntax_Const.op_LTE, uu____8006) in
                        let uu____8024 =
                          let uu____8033 =
                            let uu____8041 =
                              let uu____8047 =
                                let uu____8048 =
                                  let uu____8049 =
                                    let uu____8052 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____8053 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____8052, uu____8053) in
                                  FStar_SMTEncoding_Util.mkGT uu____8049 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____8048 in
                              quant xy uu____8047 in
                            (FStar_Syntax_Const.op_GT, uu____8041) in
                          let uu____8059 =
                            let uu____8068 =
                              let uu____8076 =
                                let uu____8082 =
                                  let uu____8083 =
                                    let uu____8084 =
                                      let uu____8087 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____8088 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____8087, uu____8088) in
                                    FStar_SMTEncoding_Util.mkGTE uu____8084 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____8083 in
                                quant xy uu____8082 in
                              (FStar_Syntax_Const.op_GTE, uu____8076) in
                            let uu____8094 =
                              let uu____8103 =
                                let uu____8111 =
                                  let uu____8117 =
                                    let uu____8118 =
                                      let uu____8119 =
                                        let uu____8122 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____8123 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____8122, uu____8123) in
                                      FStar_SMTEncoding_Util.mkSub uu____8119 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8118 in
                                  quant xy uu____8117 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____8111) in
                              let uu____8129 =
                                let uu____8138 =
                                  let uu____8146 =
                                    let uu____8152 =
                                      let uu____8153 =
                                        let uu____8154 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8154 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8153 in
                                    quant qx uu____8152 in
                                  (FStar_Syntax_Const.op_Minus, uu____8146) in
                                let uu____8160 =
                                  let uu____8169 =
                                    let uu____8177 =
                                      let uu____8183 =
                                        let uu____8184 =
                                          let uu____8185 =
                                            let uu____8188 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8189 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8188, uu____8189) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8185 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8184 in
                                      quant xy uu____8183 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8177) in
                                  let uu____8195 =
                                    let uu____8204 =
                                      let uu____8212 =
                                        let uu____8218 =
                                          let uu____8219 =
                                            let uu____8220 =
                                              let uu____8223 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8224 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8223, uu____8224) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8220 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8219 in
                                        quant xy uu____8218 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8212) in
                                    let uu____8230 =
                                      let uu____8239 =
                                        let uu____8247 =
                                          let uu____8253 =
                                            let uu____8254 =
                                              let uu____8255 =
                                                let uu____8258 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8259 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8258, uu____8259) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8255 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8254 in
                                          quant xy uu____8253 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8247) in
                                      let uu____8265 =
                                        let uu____8274 =
                                          let uu____8282 =
                                            let uu____8288 =
                                              let uu____8289 =
                                                let uu____8290 =
                                                  let uu____8293 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8294 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8293, uu____8294) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8290 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8289 in
                                            quant xy uu____8288 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8282) in
                                        let uu____8300 =
                                          let uu____8309 =
                                            let uu____8317 =
                                              let uu____8323 =
                                                let uu____8324 =
                                                  let uu____8325 =
                                                    let uu____8328 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8329 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8328, uu____8329) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8325 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8324 in
                                              quant xy uu____8323 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8317) in
                                          let uu____8335 =
                                            let uu____8344 =
                                              let uu____8352 =
                                                let uu____8358 =
                                                  let uu____8359 =
                                                    let uu____8360 =
                                                      let uu____8363 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8364 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8363,
                                                        uu____8364) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8360 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8359 in
                                                quant xy uu____8358 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8352) in
                                            let uu____8370 =
                                              let uu____8379 =
                                                let uu____8387 =
                                                  let uu____8393 =
                                                    let uu____8394 =
                                                      let uu____8395 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8395 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8394 in
                                                  quant qx uu____8393 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8387) in
                                              [uu____8379] in
                                            uu____8344 :: uu____8370 in
                                          uu____8309 :: uu____8335 in
                                        uu____8274 :: uu____8300 in
                                      uu____8239 :: uu____8265 in
                                    uu____8204 :: uu____8230 in
                                  uu____8169 :: uu____8195 in
                                uu____8138 :: uu____8160 in
                              uu____8103 :: uu____8129 in
                            uu____8068 :: uu____8094 in
                          uu____8033 :: uu____8059 in
                        uu____7998 :: uu____8024 in
                      uu____7963 :: uu____7989 in
                    uu____7932 :: uu____7954 in
                  uu____7902 :: uu____7923 in
                let mk1 l v1 =
                  let uu____8523 =
                    let uu____8528 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8560  ->
                              match uu____8560 with
                              | (l',uu____8569) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8528
                      (FStar_Option.map
                         (fun uu____8602  ->
                            match uu____8602 with | (uu____8613,b) -> b v1)) in
                  FStar_All.pipe_right uu____8523 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8654  ->
                          match uu____8654 with
                          | (l',uu____8663) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8689 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8689 with
        | (xxsym,xx) ->
            let uu____8694 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8694 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8702 =
                   let uu____8706 =
                     let uu____8707 =
                       let uu____8713 =
                         let uu____8714 =
                           let uu____8717 =
                             let uu____8718 =
                               let uu____8721 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8721) in
                             FStar_SMTEncoding_Util.mkEq uu____8718 in
                           (xx_has_type, uu____8717) in
                         FStar_SMTEncoding_Util.mkImp uu____8714 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8713) in
                     FStar_SMTEncoding_Util.mkForall uu____8707 in
                   let uu____8734 =
                     let uu____8735 =
                       let uu____8736 =
                         let uu____8737 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8737 in
                       Prims.strcat module_name uu____8736 in
                     varops.mk_unique uu____8735 in
                   (uu____8706, (Some "pretyping"), uu____8734) in
                 FStar_SMTEncoding_Util.mkAssume uu____8702)
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
    let uu____8767 =
      let uu____8768 =
        let uu____8772 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8772, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8768 in
    let uu____8774 =
      let uu____8776 =
        let uu____8777 =
          let uu____8781 =
            let uu____8782 =
              let uu____8788 =
                let uu____8789 =
                  let uu____8792 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8792) in
                FStar_SMTEncoding_Util.mkImp uu____8789 in
              ([[typing_pred]], [xx], uu____8788) in
            mkForall_fuel uu____8782 in
          (uu____8781, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8777 in
      [uu____8776] in
    uu____8767 :: uu____8774 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8820 =
      let uu____8821 =
        let uu____8825 =
          let uu____8826 =
            let uu____8832 =
              let uu____8835 =
                let uu____8837 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8837] in
              [uu____8835] in
            let uu____8840 =
              let uu____8841 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8841 tt in
            (uu____8832, [bb], uu____8840) in
          FStar_SMTEncoding_Util.mkForall uu____8826 in
        (uu____8825, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8821 in
    let uu____8852 =
      let uu____8854 =
        let uu____8855 =
          let uu____8859 =
            let uu____8860 =
              let uu____8866 =
                let uu____8867 =
                  let uu____8870 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8870) in
                FStar_SMTEncoding_Util.mkImp uu____8867 in
              ([[typing_pred]], [xx], uu____8866) in
            mkForall_fuel uu____8860 in
          (uu____8859, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8855 in
      [uu____8854] in
    uu____8820 :: uu____8852 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8904 =
        let uu____8905 =
          let uu____8909 =
            let uu____8911 =
              let uu____8913 =
                let uu____8915 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8916 =
                  let uu____8918 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8918] in
                uu____8915 :: uu____8916 in
              tt :: uu____8913 in
            tt :: uu____8911 in
          ("Prims.Precedes", uu____8909) in
        FStar_SMTEncoding_Util.mkApp uu____8905 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8904 in
    let precedes_y_x =
      let uu____8921 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8921 in
    let uu____8923 =
      let uu____8924 =
        let uu____8928 =
          let uu____8929 =
            let uu____8935 =
              let uu____8938 =
                let uu____8940 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8940] in
              [uu____8938] in
            let uu____8943 =
              let uu____8944 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8944 tt in
            (uu____8935, [bb], uu____8943) in
          FStar_SMTEncoding_Util.mkForall uu____8929 in
        (uu____8928, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8924 in
    let uu____8955 =
      let uu____8957 =
        let uu____8958 =
          let uu____8962 =
            let uu____8963 =
              let uu____8969 =
                let uu____8970 =
                  let uu____8973 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8973) in
                FStar_SMTEncoding_Util.mkImp uu____8970 in
              ([[typing_pred]], [xx], uu____8969) in
            mkForall_fuel uu____8963 in
          (uu____8962, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8958 in
      let uu____8986 =
        let uu____8988 =
          let uu____8989 =
            let uu____8993 =
              let uu____8994 =
                let uu____9000 =
                  let uu____9001 =
                    let uu____9004 =
                      let uu____9005 =
                        let uu____9007 =
                          let uu____9009 =
                            let uu____9011 =
                              let uu____9012 =
                                let uu____9015 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____9016 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____9015, uu____9016) in
                              FStar_SMTEncoding_Util.mkGT uu____9012 in
                            let uu____9017 =
                              let uu____9019 =
                                let uu____9020 =
                                  let uu____9023 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____9024 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____9023, uu____9024) in
                                FStar_SMTEncoding_Util.mkGTE uu____9020 in
                              let uu____9025 =
                                let uu____9027 =
                                  let uu____9028 =
                                    let uu____9031 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____9032 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____9031, uu____9032) in
                                  FStar_SMTEncoding_Util.mkLT uu____9028 in
                                [uu____9027] in
                              uu____9019 :: uu____9025 in
                            uu____9011 :: uu____9017 in
                          typing_pred_y :: uu____9009 in
                        typing_pred :: uu____9007 in
                      FStar_SMTEncoding_Util.mk_and_l uu____9005 in
                    (uu____9004, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____9001 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____9000) in
              mkForall_fuel uu____8994 in
            (uu____8993, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8989 in
        [uu____8988] in
      uu____8957 :: uu____8986 in
    uu____8923 :: uu____8955 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9062 =
      let uu____9063 =
        let uu____9067 =
          let uu____9068 =
            let uu____9074 =
              let uu____9077 =
                let uu____9079 = FStar_SMTEncoding_Term.boxString b in
                [uu____9079] in
              [uu____9077] in
            let uu____9082 =
              let uu____9083 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____9083 tt in
            (uu____9074, [bb], uu____9082) in
          FStar_SMTEncoding_Util.mkForall uu____9068 in
        (uu____9067, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9063 in
    let uu____9094 =
      let uu____9096 =
        let uu____9097 =
          let uu____9101 =
            let uu____9102 =
              let uu____9108 =
                let uu____9109 =
                  let uu____9112 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____9112) in
                FStar_SMTEncoding_Util.mkImp uu____9109 in
              ([[typing_pred]], [xx], uu____9108) in
            mkForall_fuel uu____9102 in
          (uu____9101, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9097 in
      [uu____9096] in
    uu____9062 :: uu____9094 in
  let mk_ref1 env reft_name uu____9134 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____9145 =
        let uu____9149 =
          let uu____9151 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9151] in
        (reft_name, uu____9149) in
      FStar_SMTEncoding_Util.mkApp uu____9145 in
    let refb =
      let uu____9154 =
        let uu____9158 =
          let uu____9160 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9160] in
        (reft_name, uu____9158) in
      FStar_SMTEncoding_Util.mkApp uu____9154 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9164 =
      let uu____9165 =
        let uu____9169 =
          let uu____9170 =
            let uu____9176 =
              let uu____9177 =
                let uu____9180 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9180) in
              FStar_SMTEncoding_Util.mkImp uu____9177 in
            ([[typing_pred]], [xx; aa], uu____9176) in
          mkForall_fuel uu____9170 in
        (uu____9169, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9165 in
    [uu____9164] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9220 =
      let uu____9221 =
        let uu____9225 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9225, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9221 in
    [uu____9220] in
  let mk_and_interp env conj uu____9236 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9253 =
      let uu____9254 =
        let uu____9258 =
          let uu____9259 =
            let uu____9265 =
              let uu____9266 =
                let uu____9269 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9269, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9266 in
            ([[l_and_a_b]], [aa; bb], uu____9265) in
          FStar_SMTEncoding_Util.mkForall uu____9259 in
        (uu____9258, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9254 in
    [uu____9253] in
  let mk_or_interp env disj uu____9293 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9310 =
      let uu____9311 =
        let uu____9315 =
          let uu____9316 =
            let uu____9322 =
              let uu____9323 =
                let uu____9326 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9326, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9323 in
            ([[l_or_a_b]], [aa; bb], uu____9322) in
          FStar_SMTEncoding_Util.mkForall uu____9316 in
        (uu____9315, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9311 in
    [uu____9310] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9367 =
      let uu____9368 =
        let uu____9372 =
          let uu____9373 =
            let uu____9379 =
              let uu____9380 =
                let uu____9383 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9383, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9380 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9379) in
          FStar_SMTEncoding_Util.mkForall uu____9373 in
        (uu____9372, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9368 in
    [uu____9367] in
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
    let uu____9430 =
      let uu____9431 =
        let uu____9435 =
          let uu____9436 =
            let uu____9442 =
              let uu____9443 =
                let uu____9446 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9446, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9443 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9442) in
          FStar_SMTEncoding_Util.mkForall uu____9436 in
        (uu____9435, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9431 in
    [uu____9430] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9491 =
      let uu____9492 =
        let uu____9496 =
          let uu____9497 =
            let uu____9503 =
              let uu____9504 =
                let uu____9507 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9507, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9504 in
            ([[l_imp_a_b]], [aa; bb], uu____9503) in
          FStar_SMTEncoding_Util.mkForall uu____9497 in
        (uu____9496, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9492 in
    [uu____9491] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9548 =
      let uu____9549 =
        let uu____9553 =
          let uu____9554 =
            let uu____9560 =
              let uu____9561 =
                let uu____9564 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9564, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9561 in
            ([[l_iff_a_b]], [aa; bb], uu____9560) in
          FStar_SMTEncoding_Util.mkForall uu____9554 in
        (uu____9553, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9549 in
    [uu____9548] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9598 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9598 in
    let uu____9600 =
      let uu____9601 =
        let uu____9605 =
          let uu____9606 =
            let uu____9612 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9612) in
          FStar_SMTEncoding_Util.mkForall uu____9606 in
        (uu____9605, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9601 in
    [uu____9600] in
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
      let uu____9652 =
        let uu____9656 =
          let uu____9658 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9658] in
        ("Valid", uu____9656) in
      FStar_SMTEncoding_Util.mkApp uu____9652 in
    let uu____9660 =
      let uu____9661 =
        let uu____9665 =
          let uu____9666 =
            let uu____9672 =
              let uu____9673 =
                let uu____9676 =
                  let uu____9677 =
                    let uu____9683 =
                      let uu____9686 =
                        let uu____9688 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9688] in
                      [uu____9686] in
                    let uu____9691 =
                      let uu____9692 =
                        let uu____9695 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9695, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9692 in
                    (uu____9683, [xx1], uu____9691) in
                  FStar_SMTEncoding_Util.mkForall uu____9677 in
                (uu____9676, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9673 in
            ([[l_forall_a_b]], [aa; bb], uu____9672) in
          FStar_SMTEncoding_Util.mkForall uu____9666 in
        (uu____9665, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9661 in
    [uu____9660] in
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
      let uu____9746 =
        let uu____9750 =
          let uu____9752 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9752] in
        ("Valid", uu____9750) in
      FStar_SMTEncoding_Util.mkApp uu____9746 in
    let uu____9754 =
      let uu____9755 =
        let uu____9759 =
          let uu____9760 =
            let uu____9766 =
              let uu____9767 =
                let uu____9770 =
                  let uu____9771 =
                    let uu____9777 =
                      let uu____9780 =
                        let uu____9782 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9782] in
                      [uu____9780] in
                    let uu____9785 =
                      let uu____9786 =
                        let uu____9789 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9789, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9786 in
                    (uu____9777, [xx1], uu____9785) in
                  FStar_SMTEncoding_Util.mkExists uu____9771 in
                (uu____9770, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9767 in
            ([[l_exists_a_b]], [aa; bb], uu____9766) in
          FStar_SMTEncoding_Util.mkForall uu____9760 in
        (uu____9759, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9755 in
    [uu____9754] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9825 =
      let uu____9826 =
        let uu____9830 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9831 = varops.mk_unique "typing_range_const" in
        (uu____9830, (Some "Range_const typing"), uu____9831) in
      FStar_SMTEncoding_Util.mkAssume uu____9826 in
    [uu____9825] in
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
          let uu____10093 =
            FStar_Util.find_opt
              (fun uu____10111  ->
                 match uu____10111 with
                 | (l,uu____10121) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____10093 with
          | None  -> []
          | Some (uu____10143,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10180 = encode_function_type_as_formula t env in
        match uu____10180 with
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
            let uu____10212 =
              (let uu____10213 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10213) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10212
            then
              let uu____10217 = new_term_constant_and_tok_from_lid env lid in
              match uu____10217 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10229 =
                      let uu____10230 = FStar_Syntax_Subst.compress t_norm in
                      uu____10230.FStar_Syntax_Syntax.n in
                    match uu____10229 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10235) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10252  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10255 -> [] in
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
              (let uu____10264 = prims.is lid in
               if uu____10264
               then
                 let vname = varops.new_fvar lid in
                 let uu____10269 = prims.mk lid vname in
                 match uu____10269 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10284 =
                    let uu____10290 = curried_arrow_formals_comp t_norm in
                    match uu____10290 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10301 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10301
                          then
                            let uu____10302 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___144_10303 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___144_10303.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___144_10303.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___144_10303.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___144_10303.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___144_10303.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___144_10303.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___144_10303.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___144_10303.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___144_10303.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___144_10303.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___144_10303.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___144_10303.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___144_10303.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___144_10303.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___144_10303.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___144_10303.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___144_10303.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___144_10303.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___144_10303.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___144_10303.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___144_10303.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___144_10303.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___144_10303.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10302
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10310 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10310)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10284 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10337 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10337 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10350 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10374  ->
                                     match uu___115_10374 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10377 =
                                           FStar_Util.prefix vars in
                                         (match uu____10377 with
                                          | (uu____10388,(xxsym,uu____10390))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10400 =
                                                let uu____10401 =
                                                  let uu____10405 =
                                                    let uu____10406 =
                                                      let uu____10412 =
                                                        let uu____10413 =
                                                          let uu____10416 =
                                                            let uu____10417 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10417 in
                                                          (vapp, uu____10416) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10413 in
                                                      ([[vapp]], vars,
                                                        uu____10412) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10406 in
                                                  (uu____10405,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10401 in
                                              [uu____10400])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10428 =
                                           FStar_Util.prefix vars in
                                         (match uu____10428 with
                                          | (uu____10439,(xxsym,uu____10441))
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
                                              let uu____10455 =
                                                let uu____10456 =
                                                  let uu____10460 =
                                                    let uu____10461 =
                                                      let uu____10467 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10467) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10461 in
                                                  (uu____10460,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10456 in
                                              [uu____10455])
                                     | uu____10476 -> [])) in
                           let uu____10477 = encode_binders None formals env1 in
                           (match uu____10477 with
                            | (vars,guards,env',decls1,uu____10493) ->
                                let uu____10500 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10505 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10505, decls1)
                                  | Some p ->
                                      let uu____10507 = encode_formula p env' in
                                      (match uu____10507 with
                                       | (g,ds) ->
                                           let uu____10514 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10514,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10500 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10523 =
                                         let uu____10527 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10527) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10523 in
                                     let uu____10532 =
                                       let vname_decl =
                                         let uu____10537 =
                                           let uu____10543 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10548  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10543,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10537 in
                                       let uu____10553 =
                                         let env2 =
                                           let uu___145_10557 = env1 in
                                           {
                                             bindings =
                                               (uu___145_10557.bindings);
                                             depth = (uu___145_10557.depth);
                                             tcenv = (uu___145_10557.tcenv);
                                             warn = (uu___145_10557.warn);
                                             cache = (uu___145_10557.cache);
                                             nolabels =
                                               (uu___145_10557.nolabels);
                                             use_zfuel_name =
                                               (uu___145_10557.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___145_10557.current_module_name)
                                           } in
                                         let uu____10558 =
                                           let uu____10559 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10559 in
                                         if uu____10558
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10553 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10569::uu____10570 ->
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
                                                   let uu____10593 =
                                                     let uu____10599 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10599) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10593 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10613 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10615 =
                                             match formals with
                                             | [] ->
                                                 let uu____10624 =
                                                   let uu____10625 =
                                                     let uu____10627 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10627 in
                                                   push_free_var env1 lid
                                                     vname uu____10625 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10624)
                                             | uu____10630 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10635 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10635 in
                                                 let name_tok_corr =
                                                   let uu____10637 =
                                                     let uu____10641 =
                                                       let uu____10642 =
                                                         let uu____10648 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10648) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10642 in
                                                     (uu____10641,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10637 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10615 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10532 with
                                      | (decls2,env2) ->
                                          let uu____10672 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10677 =
                                              encode_term res_t1 env' in
                                            match uu____10677 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10685 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10685,
                                                  decls) in
                                          (match uu____10672 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10693 =
                                                   let uu____10697 =
                                                     let uu____10698 =
                                                       let uu____10704 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10704) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10698 in
                                                   (uu____10697,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10693 in
                                               let freshness =
                                                 let uu____10713 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10713
                                                 then
                                                   let uu____10716 =
                                                     let uu____10717 =
                                                       let uu____10723 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
                                                       let uu____10729 =
                                                         varops.next_id () in
                                                       (vname, uu____10723,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10729) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10717 in
                                                   let uu____10731 =
                                                     let uu____10733 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10733] in
                                                   uu____10716 :: uu____10731
                                                 else [] in
                                               let g =
                                                 let uu____10737 =
                                                   let uu____10739 =
                                                     let uu____10741 =
                                                       let uu____10743 =
                                                         let uu____10745 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10745 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10743 in
                                                     FStar_List.append decls3
                                                       uu____10741 in
                                                   FStar_List.append decls2
                                                     uu____10739 in
                                                 FStar_List.append decls11
                                                   uu____10737 in
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
          let uu____10767 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10767 with
          | None  ->
              let uu____10790 = encode_free_var env x t t_norm [] in
              (match uu____10790 with
               | (decls,env1) ->
                   let uu____10805 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10805 with
                    | (n1,x',uu____10824) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10836) -> ((n1, x1), [], env)
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
          let uu____10869 = encode_free_var env lid t tt quals in
          match uu____10869 with
          | (decls,env1) ->
              let uu____10880 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10880
              then
                let uu____10884 =
                  let uu____10886 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10886 in
                (uu____10884, env1)
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
             (fun uu____10914  ->
                fun lb  ->
                  match uu____10914 with
                  | (decls,env1) ->
                      let uu____10926 =
                        let uu____10930 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10930
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10926 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10944 = FStar_Syntax_Util.head_and_args t in
    match uu____10944 with
    | (hd1,args) ->
        let uu____10970 =
          let uu____10971 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10971.FStar_Syntax_Syntax.n in
        (match uu____10970 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10975,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10988 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____11003  ->
      fun quals  ->
        match uu____11003 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____11052 = FStar_Util.first_N nbinders formals in
              match uu____11052 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11092  ->
                         fun uu____11093  ->
                           match (uu____11092, uu____11093) with
                           | ((formal,uu____11103),(binder,uu____11105)) ->
                               let uu____11110 =
                                 let uu____11115 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11115) in
                               FStar_Syntax_Syntax.NT uu____11110) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11120 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11134  ->
                              match uu____11134 with
                              | (x,i) ->
                                  let uu____11141 =
                                    let uu___146_11142 = x in
                                    let uu____11143 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___146_11142.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___146_11142.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11143
                                    } in
                                  (uu____11141, i))) in
                    FStar_All.pipe_right uu____11120
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11155 =
                      let uu____11157 =
                        let uu____11158 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11158.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____11157 in
                    let uu____11162 =
                      let uu____11163 = FStar_Syntax_Subst.compress body in
                      let uu____11164 =
                        let uu____11165 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11165 in
                      FStar_Syntax_Syntax.extend_app_n uu____11163
                        uu____11164 in
                    uu____11162 uu____11155 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11207 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11207
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___147_11208 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___147_11208.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___147_11208.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___147_11208.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___147_11208.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___147_11208.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___147_11208.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___147_11208.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___147_11208.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___147_11208.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___147_11208.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___147_11208.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___147_11208.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___147_11208.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___147_11208.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___147_11208.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___147_11208.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___147_11208.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___147_11208.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___147_11208.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___147_11208.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___147_11208.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___147_11208.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___147_11208.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11229 = FStar_Syntax_Util.abs_formals e in
                match uu____11229 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11278::uu____11279 ->
                         let uu____11287 =
                           let uu____11288 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11288.FStar_Syntax_Syntax.n in
                         (match uu____11287 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11315 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11315 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11341 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11341
                                   then
                                     let uu____11359 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11359 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11405  ->
                                                   fun uu____11406  ->
                                                     match (uu____11405,
                                                             uu____11406)
                                                     with
                                                     | ((x,uu____11416),
                                                        (b,uu____11418)) ->
                                                         let uu____11423 =
                                                           let uu____11428 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11428) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11423)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11430 =
                                            let uu____11441 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11441) in
                                          (uu____11430, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11476 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11476 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11528) ->
                              let uu____11533 =
                                let uu____11544 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____11544 in
                              (uu____11533, true)
                          | uu____11577 when Prims.op_Negation norm1 ->
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
                          | uu____11579 ->
                              let uu____11580 =
                                let uu____11581 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11582 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11581
                                  uu____11582 in
                              failwith uu____11580)
                     | uu____11595 ->
                         let uu____11596 =
                           let uu____11597 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11597.FStar_Syntax_Syntax.n in
                         (match uu____11596 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11624 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11624 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11642 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11642 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11690 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11718 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11718
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11725 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11766  ->
                            fun lb  ->
                              match uu____11766 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11817 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11817
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11820 =
                                      let uu____11828 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11828
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11820 with
                                    | (tok,decl,env2) ->
                                        let uu____11853 =
                                          let uu____11860 =
                                            let uu____11866 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11866, tok) in
                                          uu____11860 :: toks in
                                        (uu____11853, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11725 with
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
                        | uu____11968 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11973 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11973 vars)
                            else
                              (let uu____11975 =
                                 let uu____11979 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11979) in
                               FStar_SMTEncoding_Util.mkApp uu____11975) in
                      let uu____11984 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_11986  ->
                                 match uu___116_11986 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11987 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11990 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11990))) in
                      if uu____11984
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____12010;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____12012;
                                FStar_Syntax_Syntax.lbeff = uu____12013;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____12054 =
                                 let uu____12058 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____12058 with
                                 | (tcenv',uu____12069,e_t) ->
                                     let uu____12073 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12080 -> failwith "Impossible" in
                                     (match uu____12073 with
                                      | (e1,t_norm1) ->
                                          ((let uu___150_12089 = env1 in
                                            {
                                              bindings =
                                                (uu___150_12089.bindings);
                                              depth = (uu___150_12089.depth);
                                              tcenv = tcenv';
                                              warn = (uu___150_12089.warn);
                                              cache = (uu___150_12089.cache);
                                              nolabels =
                                                (uu___150_12089.nolabels);
                                              use_zfuel_name =
                                                (uu___150_12089.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___150_12089.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___150_12089.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____12054 with
                                | (env',e1,t_norm1) ->
                                    let uu____12096 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____12096 with
                                     | ((binders,body,uu____12108,uu____12109),curry)
                                         ->
                                         ((let uu____12116 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____12116
                                           then
                                             let uu____12117 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12118 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12117 uu____12118
                                           else ());
                                          (let uu____12120 =
                                             encode_binders None binders env' in
                                           match uu____12120 with
                                           | (vars,guards,env'1,binder_decls,uu____12136)
                                               ->
                                               let body1 =
                                                 let uu____12144 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12144
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12147 =
                                                 let uu____12152 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12152
                                                 then
                                                   let uu____12158 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12159 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12158, uu____12159)
                                                 else
                                                   (let uu____12165 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12165)) in
                                               (match uu____12147 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12179 =
                                                        let uu____12183 =
                                                          let uu____12184 =
                                                            let uu____12190 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12190) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12184 in
                                                        let uu____12196 =
                                                          let uu____12198 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12198 in
                                                        (uu____12183,
                                                          uu____12196,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12179 in
                                                    let uu____12200 =
                                                      let uu____12202 =
                                                        let uu____12204 =
                                                          let uu____12206 =
                                                            let uu____12208 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12208 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12206 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12204 in
                                                      FStar_List.append
                                                        decls1 uu____12202 in
                                                    (uu____12200, env1))))))
                           | uu____12211 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12230 = varops.fresh "fuel" in
                             (uu____12230, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12233 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12272  ->
                                     fun uu____12273  ->
                                       match (uu____12272, uu____12273) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12355 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12355 in
                                           let gtok =
                                             let uu____12357 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12357 in
                                           let env3 =
                                             let uu____12359 =
                                               let uu____12361 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12361 in
                                             push_free_var env2 flid gtok
                                               uu____12359 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12233 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12447
                                 t_norm uu____12449 =
                                 match (uu____12447, uu____12449) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12476;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12477;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12494 =
                                       let uu____12498 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12498 with
                                       | (tcenv',uu____12513,e_t) ->
                                           let uu____12517 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12524 ->
                                                 failwith "Impossible" in
                                           (match uu____12517 with
                                            | (e1,t_norm1) ->
                                                ((let uu___151_12533 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___151_12533.bindings);
                                                    depth =
                                                      (uu___151_12533.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___151_12533.warn);
                                                    cache =
                                                      (uu___151_12533.cache);
                                                    nolabels =
                                                      (uu___151_12533.nolabels);
                                                    use_zfuel_name =
                                                      (uu___151_12533.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___151_12533.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___151_12533.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12494 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12543 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12543
                                            then
                                              let uu____12544 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12545 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12546 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12544 uu____12545
                                                uu____12546
                                            else ());
                                           (let uu____12548 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12548 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12570 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12570
                                                  then
                                                    let uu____12571 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12572 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12573 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12574 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12571 uu____12572
                                                      uu____12573 uu____12574
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12578 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12578 with
                                                  | (vars,guards,env'1,binder_decls,uu____12596)
                                                      ->
                                                      let decl_g =
                                                        let uu____12604 =
                                                          let uu____12610 =
                                                            let uu____12612 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12612 in
                                                          (g, uu____12610,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12604 in
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
                                                        let uu____12627 =
                                                          let uu____12631 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12631) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12627 in
                                                      let gsapp =
                                                        let uu____12637 =
                                                          let uu____12641 =
                                                            let uu____12643 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12643 ::
                                                              vars_tm in
                                                          (g, uu____12641) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12637 in
                                                      let gmax =
                                                        let uu____12647 =
                                                          let uu____12651 =
                                                            let uu____12653 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12653 ::
                                                              vars_tm in
                                                          (g, uu____12651) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12647 in
                                                      let body1 =
                                                        let uu____12657 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12657
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12659 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12659 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12670
                                                               =
                                                               let uu____12674
                                                                 =
                                                                 let uu____12675
                                                                   =
                                                                   let uu____12683
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
                                                                    uu____12683) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12675 in
                                                               let uu____12694
                                                                 =
                                                                 let uu____12696
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12696 in
                                                               (uu____12674,
                                                                 uu____12694,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12670 in
                                                           let eqn_f =
                                                             let uu____12699
                                                               =
                                                               let uu____12703
                                                                 =
                                                                 let uu____12704
                                                                   =
                                                                   let uu____12710
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12710) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12704 in
                                                               (uu____12703,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12699 in
                                                           let eqn_g' =
                                                             let uu____12718
                                                               =
                                                               let uu____12722
                                                                 =
                                                                 let uu____12723
                                                                   =
                                                                   let uu____12729
                                                                    =
                                                                    let uu____12730
                                                                    =
                                                                    let uu____12733
                                                                    =
                                                                    let uu____12734
                                                                    =
                                                                    let uu____12738
                                                                    =
                                                                    let uu____12740
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12740
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12738) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12734 in
                                                                    (gsapp,
                                                                    uu____12733) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12730 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12729) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12723 in
                                                               (uu____12722,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12718 in
                                                           let uu____12752 =
                                                             let uu____12757
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12757
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12774)
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
                                                                    let uu____12789
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12789
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12792
                                                                    =
                                                                    let uu____12796
                                                                    =
                                                                    let uu____12797
                                                                    =
                                                                    let uu____12803
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12803) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12797 in
                                                                    (uu____12796,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12792 in
                                                                 let uu____12814
                                                                   =
                                                                   let uu____12818
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12818
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12826
                                                                    =
                                                                    let uu____12828
                                                                    =
                                                                    let uu____12829
                                                                    =
                                                                    let uu____12833
                                                                    =
                                                                    let uu____12834
                                                                    =
                                                                    let uu____12840
                                                                    =
                                                                    let uu____12841
                                                                    =
                                                                    let uu____12844
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12844,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12841 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12840) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12834 in
                                                                    (uu____12833,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12829 in
                                                                    [uu____12828] in
                                                                    (d3,
                                                                    uu____12826) in
                                                                 (match uu____12814
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12752
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
                               let uu____12879 =
                                 let uu____12886 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12922  ->
                                      fun uu____12923  ->
                                        match (uu____12922, uu____12923) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____13009 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____13009 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12886 in
                               (match uu____12879 with
                                | (decls2,eqns,env01) ->
                                    let uu____13049 =
                                      let isDeclFun uu___117_13057 =
                                        match uu___117_13057 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____13058 -> true
                                        | uu____13064 -> false in
                                      let uu____13065 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____13065
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____13049 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____13092 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____13092
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
        let uu____13125 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13125 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____13128 = encode_sigelt' env se in
      match uu____13128 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13138 =
                  let uu____13139 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13139 in
                [uu____13138]
            | uu____13140 ->
                let uu____13141 =
                  let uu____13143 =
                    let uu____13144 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13144 in
                  uu____13143 :: g in
                let uu____13145 =
                  let uu____13147 =
                    let uu____13148 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13148 in
                  [uu____13147] in
                FStar_List.append uu____13141 uu____13145 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13156 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13159 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13161 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13163 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13171 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13174 =
            let uu____13175 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13175 Prims.op_Negation in
          if uu____13174
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13195 ->
                   let uu____13196 =
                     let uu____13199 =
                       let uu____13200 =
                         let uu____13215 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13215) in
                       FStar_Syntax_Syntax.Tm_abs uu____13200 in
                     FStar_Syntax_Syntax.mk uu____13199 in
                   uu____13196 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13268 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13268 with
               | (aname,atok,env2) ->
                   let uu____13278 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13278 with
                    | (formals,uu____13288) ->
                        let uu____13295 =
                          let uu____13298 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13298 env2 in
                        (match uu____13295 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13306 =
                                 let uu____13307 =
                                   let uu____13313 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13321  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13313,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13307 in
                               [uu____13306;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13328 =
                               let aux uu____13357 uu____13358 =
                                 match (uu____13357, uu____13358) with
                                 | ((bv,uu____13385),(env3,acc_sorts,acc)) ->
                                     let uu____13406 = gen_term_var env3 bv in
                                     (match uu____13406 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13328 with
                              | (uu____13444,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13458 =
                                      let uu____13462 =
                                        let uu____13463 =
                                          let uu____13469 =
                                            let uu____13470 =
                                              let uu____13473 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13473) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13470 in
                                          ([[app]], xs_sorts, uu____13469) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13463 in
                                      (uu____13462, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13458 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13485 =
                                      let uu____13489 =
                                        let uu____13490 =
                                          let uu____13496 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13496) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13490 in
                                      (uu____13489,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13485 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13506 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13506 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13522,uu____13523)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13524 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13524 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13535,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13540 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13542  ->
                      match uu___118_13542 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13543 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13546 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13547 -> false)) in
            Prims.op_Negation uu____13540 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13553 = encode_top_level_val env fv t quals in
             match uu____13553 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13565 =
                   let uu____13567 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13567 in
                 (uu____13565, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13572 = encode_formula f env in
          (match uu____13572 with
           | (f1,decls) ->
               let g =
                 let uu____13581 =
                   let uu____13582 =
                     let uu____13586 =
                       let uu____13588 =
                         let uu____13589 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13589 in
                       Some uu____13588 in
                     let uu____13590 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13586, uu____13590) in
                   FStar_SMTEncoding_Util.mkAssume uu____13582 in
                 [uu____13581] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13594,uu____13595) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13601 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13608 =
                       let uu____13613 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13613.FStar_Syntax_Syntax.fv_name in
                     uu____13608.FStar_Syntax_Syntax.v in
                   let uu____13617 =
                     let uu____13618 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13618 in
                   if uu____13617
                   then
                     let val_decl =
                       let uu___152_13633 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___152_13633.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___152_13633.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___152_13633.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13637 = encode_sigelt' env1 val_decl in
                     match uu____13637 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____13601 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13654,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13656;
                          FStar_Syntax_Syntax.lbtyp = uu____13657;
                          FStar_Syntax_Syntax.lbeff = uu____13658;
                          FStar_Syntax_Syntax.lbdef = uu____13659;_}::[]),uu____13660,uu____13661)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13675 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13675 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13698 =
                   let uu____13700 =
                     let uu____13701 =
                       let uu____13705 =
                         let uu____13706 =
                           let uu____13712 =
                             let uu____13713 =
                               let uu____13716 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13716) in
                             FStar_SMTEncoding_Util.mkEq uu____13713 in
                           ([[b2t_x]], [xx], uu____13712) in
                         FStar_SMTEncoding_Util.mkForall uu____13706 in
                       (uu____13705, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13701 in
                   [uu____13700] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13698 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13733,uu____13734,uu____13735)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_13741  ->
                  match uu___119_13741 with
                  | FStar_Syntax_Syntax.Discriminator uu____13742 -> true
                  | uu____13743 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13745,lids,uu____13747) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13754 =
                     let uu____13755 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13755.FStar_Ident.idText in
                   uu____13754 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_13757  ->
                     match uu___120_13757 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13758 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13761,uu____13762)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_13772  ->
                  match uu___121_13772 with
                  | FStar_Syntax_Syntax.Projector uu____13773 -> true
                  | uu____13776 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13783 = try_lookup_free_var env l in
          (match uu____13783 with
           | Some uu____13787 -> ([], env)
           | None  ->
               let se1 =
                 let uu___153_13790 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___153_13790.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___153_13790.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13796,uu____13797) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13809) ->
          let uu____13814 = encode_sigelts env ses in
          (match uu____13814 with
           | (g,env1) ->
               let uu____13824 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_13834  ->
                         match uu___122_13834 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13835;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13836;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13837;_}
                             -> false
                         | uu____13839 -> true)) in
               (match uu____13824 with
                | (g',inversions) ->
                    let uu____13848 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_13858  ->
                              match uu___123_13858 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13859 ->
                                  true
                              | uu____13865 -> false)) in
                    (match uu____13848 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13876,tps,k,uu____13879,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_13889  ->
                    match uu___124_13889 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13890 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13897 = c in
              match uu____13897 with
              | (name,args,uu____13901,uu____13902,uu____13903) ->
                  let uu____13906 =
                    let uu____13907 =
                      let uu____13913 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13920  ->
                                match uu____13920 with
                                | (uu____13924,sort,uu____13926) -> sort)) in
                      (name, uu____13913, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13907 in
                  [uu____13906]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13944 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13947 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13947 FStar_Option.isNone)) in
            if uu____13944
            then []
            else
              (let uu____13964 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13964 with
               | (xxsym,xx) ->
                   let uu____13970 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13981  ->
                             fun l  ->
                               match uu____13981 with
                               | (out,decls) ->
                                   let uu____13993 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13993 with
                                    | (uu____13999,data_t) ->
                                        let uu____14001 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____14001 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____14030 =
                                                 let uu____14031 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____14031.FStar_Syntax_Syntax.n in
                                               match uu____14030 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____14039,indices) ->
                                                   indices
                                               | uu____14055 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____14067  ->
                                                         match uu____14067
                                                         with
                                                         | (x,uu____14071) ->
                                                             let uu____14072
                                                               =
                                                               let uu____14073
                                                                 =
                                                                 let uu____14077
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____14077,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14073 in
                                                             push_term_var
                                                               env1 x
                                                               uu____14072)
                                                    env) in
                                             let uu____14079 =
                                               encode_args indices env1 in
                                             (match uu____14079 with
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
                                                      let uu____14099 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14107
                                                                 =
                                                                 let uu____14110
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____14110,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14107)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____14099
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____14112 =
                                                      let uu____14113 =
                                                        let uu____14116 =
                                                          let uu____14117 =
                                                            let uu____14120 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____14120,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14117 in
                                                        (out, uu____14116) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14113 in
                                                    (uu____14112,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13970 with
                    | (data_ax,decls) ->
                        let uu____14128 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14128 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14139 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14139 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14142 =
                                 let uu____14146 =
                                   let uu____14147 =
                                     let uu____14153 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14161 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14153,
                                       uu____14161) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14147 in
                                 let uu____14169 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14146, (Some "inversion axiom"),
                                   uu____14169) in
                               FStar_SMTEncoding_Util.mkAssume uu____14142 in
                             let pattern_guarded_inversion =
                               let uu____14173 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14173
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14181 =
                                   let uu____14182 =
                                     let uu____14186 =
                                       let uu____14187 =
                                         let uu____14193 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14201 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14193, uu____14201) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14187 in
                                     let uu____14209 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14186, (Some "inversion axiom"),
                                       uu____14209) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14182 in
                                 [uu____14181]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14212 =
            let uu____14220 =
              let uu____14221 = FStar_Syntax_Subst.compress k in
              uu____14221.FStar_Syntax_Syntax.n in
            match uu____14220 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14250 -> (tps, k) in
          (match uu____14212 with
           | (formals,res) ->
               let uu____14265 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14265 with
                | (formals1,res1) ->
                    let uu____14272 = encode_binders None formals1 env in
                    (match uu____14272 with
                     | (vars,guards,env',binder_decls,uu____14287) ->
                         let uu____14294 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14294 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14307 =
                                  let uu____14311 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14311) in
                                FStar_SMTEncoding_Util.mkApp uu____14307 in
                              let uu____14316 =
                                let tname_decl =
                                  let uu____14322 =
                                    let uu____14323 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14338  ->
                                              match uu____14338 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14346 = varops.next_id () in
                                    (tname, uu____14323,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14346, false) in
                                  constructor_or_logic_type_decl uu____14322 in
                                let uu____14351 =
                                  match vars with
                                  | [] ->
                                      let uu____14358 =
                                        let uu____14359 =
                                          let uu____14361 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14361 in
                                        push_free_var env1 t tname
                                          uu____14359 in
                                      ([], uu____14358)
                                  | uu____14365 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14371 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14371 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14380 =
                                          let uu____14384 =
                                            let uu____14385 =
                                              let uu____14393 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14393) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14385 in
                                          (uu____14384,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14380 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14351 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14316 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14416 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14416 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14430 =
                                               let uu____14431 =
                                                 let uu____14435 =
                                                   let uu____14436 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14436 in
                                                 (uu____14435,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14431 in
                                             [uu____14430]
                                           else [] in
                                         let uu____14439 =
                                           let uu____14441 =
                                             let uu____14443 =
                                               let uu____14444 =
                                                 let uu____14448 =
                                                   let uu____14449 =
                                                     let uu____14455 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14455) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14449 in
                                                 (uu____14448, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14444 in
                                             [uu____14443] in
                                           FStar_List.append karr uu____14441 in
                                         FStar_List.append decls1 uu____14439 in
                                   let aux =
                                     let uu____14464 =
                                       let uu____14466 =
                                         inversion_axioms tapp vars in
                                       let uu____14468 =
                                         let uu____14470 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14470] in
                                       FStar_List.append uu____14466
                                         uu____14468 in
                                     FStar_List.append kindingAx uu____14464 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14475,uu____14476,uu____14477,uu____14478,uu____14479)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14484,t,uu____14486,n_tps,uu____14488) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14493 = new_term_constant_and_tok_from_lid env d in
          (match uu____14493 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14504 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14504 with
                | (formals,t_res) ->
                    let uu____14526 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14526 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14535 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14535 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14573 =
                                            mk_term_projector_name d x in
                                          (uu____14573,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14575 =
                                  let uu____14585 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14585, true) in
                                FStar_All.pipe_right uu____14575
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
                              let uu____14607 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14607 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14615::uu____14616 ->
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
                                         let uu____14641 =
                                           let uu____14647 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14647) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14641
                                     | uu____14660 -> tok_typing in
                                   let uu____14665 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14665 with
                                    | (vars',guards',env'',decls_formals,uu____14680)
                                        ->
                                        let uu____14687 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14687 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14706 ->
                                                   let uu____14710 =
                                                     let uu____14711 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14711 in
                                                   [uu____14710] in
                                             let encode_elim uu____14718 =
                                               let uu____14719 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14719 with
                                               | (head1,args) ->
                                                   let uu____14748 =
                                                     let uu____14749 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14749.FStar_Syntax_Syntax.n in
                                                   (match uu____14748 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____14756;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14757;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14758;_},uu____14759)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14769 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14769
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
                                                                 | uu____14795
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14803
                                                                    =
                                                                    let uu____14804
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14804 in
                                                                    if
                                                                    uu____14803
                                                                    then
                                                                    let uu____14811
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14811]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14813
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14826
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14826
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14848
                                                                    =
                                                                    let uu____14852
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14852 in
                                                                    (match uu____14848
                                                                    with
                                                                    | 
                                                                    (uu____14859,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14865
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14865
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14867
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14867
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
                                                             (match uu____14813
                                                              with
                                                              | (uu____14875,arg_vars,elim_eqns_or_guards,uu____14878)
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
                                                                    let uu____14897
                                                                    =
                                                                    let uu____14901
                                                                    =
                                                                    let uu____14902
                                                                    =
                                                                    let uu____14908
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14914
                                                                    =
                                                                    let uu____14915
                                                                    =
                                                                    let uu____14918
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14918) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14915 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14908,
                                                                    uu____14914) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14902 in
                                                                    (uu____14901,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14897 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14931
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14931,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14933
                                                                    =
                                                                    let uu____14937
                                                                    =
                                                                    let uu____14938
                                                                    =
                                                                    let uu____14944
                                                                    =
                                                                    let uu____14947
                                                                    =
                                                                    let uu____14949
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14949] in
                                                                    [uu____14947] in
                                                                    let uu____14952
                                                                    =
                                                                    let uu____14953
                                                                    =
                                                                    let uu____14956
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14957
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14956,
                                                                    uu____14957) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14953 in
                                                                    (uu____14944,
                                                                    [x],
                                                                    uu____14952) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14938 in
                                                                    let uu____14967
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14937,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14967) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14933
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14972
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
                                                                    (let uu____14987
                                                                    =
                                                                    let uu____14988
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14988
                                                                    dapp1 in
                                                                    [uu____14987]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14972
                                                                    FStar_List.flatten in
                                                                    let uu____14992
                                                                    =
                                                                    let uu____14996
                                                                    =
                                                                    let uu____14997
                                                                    =
                                                                    let uu____15003
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15009
                                                                    =
                                                                    let uu____15010
                                                                    =
                                                                    let uu____15013
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15013) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15010 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15003,
                                                                    uu____15009) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14997 in
                                                                    (uu____14996,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14992) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____15029 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15029
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
                                                                 | uu____15055
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15063
                                                                    =
                                                                    let uu____15064
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15064 in
                                                                    if
                                                                    uu____15063
                                                                    then
                                                                    let uu____15071
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15071]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15073
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15086
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15086
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15108
                                                                    =
                                                                    let uu____15112
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15112 in
                                                                    (match uu____15108
                                                                    with
                                                                    | 
                                                                    (uu____15119,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15125
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15125
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15127
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15127
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
                                                             (match uu____15073
                                                              with
                                                              | (uu____15135,arg_vars,elim_eqns_or_guards,uu____15138)
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
                                                                    let uu____15157
                                                                    =
                                                                    let uu____15161
                                                                    =
                                                                    let uu____15162
                                                                    =
                                                                    let uu____15168
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15174
                                                                    =
                                                                    let uu____15175
                                                                    =
                                                                    let uu____15178
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15178) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15175 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15168,
                                                                    uu____15174) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15162 in
                                                                    (uu____15161,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15157 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15191
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15191,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15193
                                                                    =
                                                                    let uu____15197
                                                                    =
                                                                    let uu____15198
                                                                    =
                                                                    let uu____15204
                                                                    =
                                                                    let uu____15207
                                                                    =
                                                                    let uu____15209
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15209] in
                                                                    [uu____15207] in
                                                                    let uu____15212
                                                                    =
                                                                    let uu____15213
                                                                    =
                                                                    let uu____15216
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15217
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15216,
                                                                    uu____15217) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15213 in
                                                                    (uu____15204,
                                                                    [x],
                                                                    uu____15212) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15198 in
                                                                    let uu____15227
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15197,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15227) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15193
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15232
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
                                                                    (let uu____15247
                                                                    =
                                                                    let uu____15248
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15248
                                                                    dapp1 in
                                                                    [uu____15247]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15232
                                                                    FStar_List.flatten in
                                                                    let uu____15252
                                                                    =
                                                                    let uu____15256
                                                                    =
                                                                    let uu____15257
                                                                    =
                                                                    let uu____15263
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15269
                                                                    =
                                                                    let uu____15270
                                                                    =
                                                                    let uu____15273
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15273) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15270 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15263,
                                                                    uu____15269) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15257 in
                                                                    (uu____15256,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15252) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15283 ->
                                                        ((let uu____15285 =
                                                            let uu____15286 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15287 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15286
                                                              uu____15287 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15285);
                                                         ([], []))) in
                                             let uu____15290 = encode_elim () in
                                             (match uu____15290 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15302 =
                                                      let uu____15304 =
                                                        let uu____15306 =
                                                          let uu____15308 =
                                                            let uu____15310 =
                                                              let uu____15311
                                                                =
                                                                let uu____15317
                                                                  =
                                                                  let uu____15319
                                                                    =
                                                                    let uu____15320
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15320 in
                                                                  Some
                                                                    uu____15319 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15317) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15311 in
                                                            [uu____15310] in
                                                          let uu____15323 =
                                                            let uu____15325 =
                                                              let uu____15327
                                                                =
                                                                let uu____15329
                                                                  =
                                                                  let uu____15331
                                                                    =
                                                                    let uu____15333
                                                                    =
                                                                    let uu____15335
                                                                    =
                                                                    let uu____15336
                                                                    =
                                                                    let uu____15340
                                                                    =
                                                                    let uu____15341
                                                                    =
                                                                    let uu____15347
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15347) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15341 in
                                                                    (uu____15340,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15336 in
                                                                    let uu____15354
                                                                    =
                                                                    let uu____15356
                                                                    =
                                                                    let uu____15357
                                                                    =
                                                                    let uu____15361
                                                                    =
                                                                    let uu____15362
                                                                    =
                                                                    let uu____15368
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____15374
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15368,
                                                                    uu____15374) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15362 in
                                                                    (uu____15361,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15357 in
                                                                    [uu____15356] in
                                                                    uu____15335
                                                                    ::
                                                                    uu____15354 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15333 in
                                                                  FStar_List.append
                                                                    uu____15331
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15329 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15327 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15325 in
                                                          FStar_List.append
                                                            uu____15308
                                                            uu____15323 in
                                                        FStar_List.append
                                                          decls3 uu____15306 in
                                                      FStar_List.append
                                                        decls2 uu____15304 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15302 in
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
           (fun uu____15395  ->
              fun se  ->
                match uu____15395 with
                | (g,env1) ->
                    let uu____15407 = encode_sigelt env1 se in
                    (match uu____15407 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15443 =
        match uu____15443 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15461 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____15466 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15466
                   then
                     let uu____15467 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15468 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15469 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15467 uu____15468 uu____15469
                   else ());
                  (let uu____15471 = encode_term t1 env1 in
                   match uu____15471 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15481 =
                         let uu____15485 =
                           let uu____15486 =
                             let uu____15487 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15487
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15486 in
                         new_term_constant_from_string env1 x uu____15485 in
                       (match uu____15481 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15498 = FStar_Options.log_queries () in
                              if uu____15498
                              then
                                let uu____15500 =
                                  let uu____15501 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15502 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15503 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15501 uu____15502 uu____15503 in
                                Some uu____15500
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15514,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15523 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15523 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15536,se,uu____15538) ->
                 let uu____15541 = encode_sigelt env1 se in
                 (match uu____15541 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15551,se) ->
                 let uu____15555 = encode_sigelt env1 se in
                 (match uu____15555 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15565 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15565 with | (uu____15577,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15622  ->
            match uu____15622 with
            | (l,uu____15629,uu____15630) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15651  ->
            match uu____15651 with
            | (l,uu____15659,uu____15660) ->
                let uu____15665 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39) (
                    fst l) in
                let uu____15666 =
                  let uu____15668 =
                    let uu____15669 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15669 in
                  [uu____15668] in
                uu____15665 :: uu____15666)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15680 =
      let uu____15682 =
        let uu____15683 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15685 =
          let uu____15686 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15686 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15683;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15685
        } in
      [uu____15682] in
    FStar_ST.write last_env uu____15680
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15696 = FStar_ST.read last_env in
      match uu____15696 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15702 ->
          let uu___154_15704 = e in
          let uu____15705 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___154_15704.bindings);
            depth = (uu___154_15704.depth);
            tcenv;
            warn = (uu___154_15704.warn);
            cache = (uu___154_15704.cache);
            nolabels = (uu___154_15704.nolabels);
            use_zfuel_name = (uu___154_15704.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15704.encode_non_total_function_typ);
            current_module_name = uu____15705
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15709 = FStar_ST.read last_env in
    match uu____15709 with
    | [] -> failwith "Empty env stack"
    | uu____15714::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15722  ->
    let uu____15723 = FStar_ST.read last_env in
    match uu____15723 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___155_15734 = hd1 in
          {
            bindings = (uu___155_15734.bindings);
            depth = (uu___155_15734.depth);
            tcenv = (uu___155_15734.tcenv);
            warn = (uu___155_15734.warn);
            cache = refs;
            nolabels = (uu___155_15734.nolabels);
            use_zfuel_name = (uu___155_15734.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_15734.encode_non_total_function_typ);
            current_module_name = (uu___155_15734.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15740  ->
    let uu____15741 = FStar_ST.read last_env in
    match uu____15741 with
    | [] -> failwith "Popping an empty stack"
    | uu____15746::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15754  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15757  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15760  ->
    let uu____15761 = FStar_ST.read last_env in
    match uu____15761 with
    | hd1::uu____15767::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15773 -> failwith "Impossible"
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
        | (uu____15822::uu____15823,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___156_15827 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___156_15827.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___156_15827.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___156_15827.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15828 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15839 =
        let uu____15841 =
          let uu____15842 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15842 in
        let uu____15843 = open_fact_db_tags env in uu____15841 :: uu____15843 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15839
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
      let uu____15858 = encode_sigelt env se in
      match uu____15858 with
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
        let uu____15883 = FStar_Options.log_queries () in
        if uu____15883
        then
          let uu____15885 =
            let uu____15886 =
              let uu____15887 =
                let uu____15888 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15888 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15887 in
            FStar_SMTEncoding_Term.Caption uu____15886 in
          uu____15885 :: decls
        else decls in
      let env =
        let uu____15895 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15895 tcenv in
      let uu____15896 = encode_top_level_facts env se in
      match uu____15896 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15905 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15905))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15916 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15916
       then
         let uu____15917 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15917
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15938  ->
                 fun se  ->
                   match uu____15938 with
                   | (g,env2) ->
                       let uu____15950 = encode_top_level_facts env2 se in
                       (match uu____15950 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15963 =
         encode_signature
           (let uu___157_15967 = env in
            {
              bindings = (uu___157_15967.bindings);
              depth = (uu___157_15967.depth);
              tcenv = (uu___157_15967.tcenv);
              warn = false;
              cache = (uu___157_15967.cache);
              nolabels = (uu___157_15967.nolabels);
              use_zfuel_name = (uu___157_15967.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___157_15967.encode_non_total_function_typ);
              current_module_name = (uu___157_15967.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15963 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15979 = FStar_Options.log_queries () in
             if uu____15979
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___158_15984 = env1 in
               {
                 bindings = (uu___158_15984.bindings);
                 depth = (uu___158_15984.depth);
                 tcenv = (uu___158_15984.tcenv);
                 warn = true;
                 cache = (uu___158_15984.cache);
                 nolabels = (uu___158_15984.nolabels);
                 use_zfuel_name = (uu___158_15984.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___158_15984.encode_non_total_function_typ);
                 current_module_name = (uu___158_15984.current_module_name)
               });
            (let uu____15986 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15986
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
        (let uu____16021 =
           let uu____16022 = FStar_TypeChecker_Env.current_module tcenv in
           uu____16022.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16021);
        (let env =
           let uu____16024 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____16024 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____16031 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16052 = aux rest in
                 (match uu____16052 with
                  | (out,rest1) ->
                      let t =
                        let uu____16070 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____16070 with
                        | Some uu____16074 ->
                            let uu____16075 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16075
                              x.FStar_Syntax_Syntax.sort
                        | uu____16076 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____16079 =
                        let uu____16081 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___159_16082 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___159_16082.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___159_16082.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16081 :: out in
                      (uu____16079, rest1))
             | uu____16085 -> ([], bindings1) in
           let uu____16089 = aux bindings in
           match uu____16089 with
           | (closing,bindings1) ->
               let uu____16103 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16103, bindings1) in
         match uu____16031 with
         | (q1,bindings1) ->
             let uu____16116 =
               let uu____16119 =
                 FStar_List.filter
                   (fun uu___125_16121  ->
                      match uu___125_16121 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16122 ->
                          false
                      | uu____16126 -> true) bindings1 in
               encode_env_bindings env uu____16119 in
             (match uu____16116 with
              | (env_decls,env1) ->
                  ((let uu____16137 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16137
                    then
                      let uu____16138 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16138
                    else ());
                   (let uu____16140 = encode_formula q1 env1 in
                    match uu____16140 with
                    | (phi,qdecls) ->
                        let uu____16152 =
                          let uu____16155 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16155 phi in
                        (match uu____16152 with
                         | (labels,phi1) ->
                             let uu____16165 = encode_labels labels in
                             (match uu____16165 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____16186 =
                                      let uu____16190 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16191 =
                                        varops.mk_unique "@query" in
                                      (uu____16190, (Some "query"),
                                        uu____16191) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16186 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16204 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16204 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16206 = encode_formula q env in
       match uu____16206 with
       | (f,uu____16210) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16212) -> true
             | uu____16215 -> false)))