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
        (let uu____2307 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2307
         then
           let uu____2308 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2308
         else ());
        (let uu____2310 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2346  ->
                   fun b  ->
                     match uu____2346 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2389 =
                           let x = unmangle (fst b) in
                           let uu____2398 = gen_term_var env1 x in
                           match uu____2398 with
                           | (xxsym,xx,env') ->
                               let uu____2412 =
                                 let uu____2415 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2415 env1 xx in
                               (match uu____2412 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2389 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2310 with
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
          let uu____2503 = encode_term t env in
          match uu____2503 with
          | (t1,decls) ->
              let uu____2510 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2510, decls)
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
          let uu____2518 = encode_term t env in
          match uu____2518 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2527 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2527, decls)
               | Some f ->
                   let uu____2529 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2529, decls))
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
        let uu____2535 = encode_args args_e env in
        match uu____2535 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2547 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____2554 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____2554 in
            let binary arg_tms1 =
              let uu____2563 =
                let uu____2564 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____2564 in
              let uu____2565 =
                let uu____2566 =
                  let uu____2567 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2567 in
                FStar_SMTEncoding_Term.unboxInt uu____2566 in
              (uu____2563, uu____2565) in
            let mk_default uu____2572 =
              let uu____2573 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2573 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____2618 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2618
              then
                let uu____2619 = let uu____2620 = mk_args ts in op uu____2620 in
                FStar_All.pipe_right uu____2619 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____2643 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____2643
              then
                let uu____2644 = binary ts in
                match uu____2644 with
                | (t1,t2) ->
                    let uu____2649 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____2649
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2652 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____2652
                 then
                   let uu____2653 = op (binary ts) in
                   FStar_All.pipe_right uu____2653
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
            let uu____2743 =
              let uu____2749 =
                FStar_List.tryFind
                  (fun uu____2761  ->
                     match uu____2761 with
                     | (l,uu____2768) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____2749 FStar_Util.must in
            (match uu____2743 with
             | (uu____2793,op) ->
                 let uu____2801 = op arg_tms in (uu____2801, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2808 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2808
       then
         let uu____2809 = FStar_Syntax_Print.tag_of_term t in
         let uu____2810 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2811 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2809 uu____2810
           uu____2811
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2815 ->
           let uu____2836 =
             let uu____2837 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2838 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2839 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2840 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2837
               uu____2838 uu____2839 uu____2840 in
           failwith uu____2836
       | FStar_Syntax_Syntax.Tm_unknown  ->
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
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2851 =
             let uu____2852 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2852 in
           failwith uu____2851
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2857) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2887) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2896 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2896, [])
       | FStar_Syntax_Syntax.Tm_type uu____2902 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2905) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2911 = encode_const c in (uu____2911, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2926 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2926 with
            | (binders1,res) ->
                let uu____2933 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2933
                then
                  let uu____2936 = encode_binders None binders1 env in
                  (match uu____2936 with
                   | (vars,guards,env',decls,uu____2951) ->
                       let fsym =
                         let uu____2961 = varops.fresh "f" in
                         (uu____2961, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2964 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_2968 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_2968.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_2968.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_2968.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_2968.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_2968.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_2968.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_2968.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_2968.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_2968.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_2968.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_2968.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_2968.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_2968.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_2968.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_2968.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_2968.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_2968.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_2968.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_2968.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_2968.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_2968.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_2968.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_2968.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2964 with
                        | (pre_opt,res_t) ->
                            let uu____2975 =
                              encode_term_pred None res_t env' app in
                            (match uu____2975 with
                             | (res_pred,decls') ->
                                 let uu____2982 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2989 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2989, [])
                                   | Some pre ->
                                       let uu____2992 =
                                         encode_formula pre env' in
                                       (match uu____2992 with
                                        | (guard,decls0) ->
                                            let uu____3000 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3000, decls0)) in
                                 (match uu____2982 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3008 =
                                          let uu____3014 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3014) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3008 in
                                      let cvars =
                                        let uu____3024 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3024
                                          (FStar_List.filter
                                             (fun uu____3030  ->
                                                match uu____3030 with
                                                | (x,uu____3034) ->
                                                    x <> (fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3045 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3045 with
                                       | Some cache_entry ->
                                           let uu____3050 =
                                             let uu____3051 =
                                               let uu____3055 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3055) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3051 in
                                           (uu____3050,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____3066 =
                                               let uu____3067 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3067 in
                                             varops.mk_unique uu____3066 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars in
                                           let caption =
                                             let uu____3074 =
                                               FStar_Options.log_queries () in
                                             if uu____3074
                                             then
                                               let uu____3076 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____3076
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3082 =
                                               let uu____3086 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3086) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3082 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3094 =
                                               let uu____3098 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3098, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3094 in
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
                                             let uu____3111 =
                                               let uu____3115 =
                                                 let uu____3116 =
                                                   let uu____3122 =
                                                     let uu____3123 =
                                                       let uu____3126 =
                                                         let uu____3127 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3127 in
                                                       (f_has_t, uu____3126) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3123 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3122) in
                                                 mkForall_fuel uu____3116 in
                                               (uu____3115,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3111 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3140 =
                                               let uu____3144 =
                                                 let uu____3145 =
                                                   let uu____3151 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3151) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3145 in
                                               (uu____3144, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3140 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3165 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3165);
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
                     let uu____3176 =
                       let uu____3180 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3180, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3176 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3189 =
                       let uu____3193 =
                         let uu____3194 =
                           let uu____3200 =
                             let uu____3201 =
                               let uu____3204 =
                                 let uu____3205 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3205 in
                               (f_has_t, uu____3204) in
                             FStar_SMTEncoding_Util.mkImp uu____3201 in
                           ([[f_has_t]], [fsym], uu____3200) in
                         mkForall_fuel uu____3194 in
                       (uu____3193, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3189 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3219 ->
           let uu____3224 =
             let uu____3227 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3227 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3232;
                 FStar_Syntax_Syntax.pos = uu____3233;
                 FStar_Syntax_Syntax.vars = uu____3234;_} ->
                 let uu____3241 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____3241 with
                  | (b,f1) ->
                      let uu____3255 =
                        let uu____3256 = FStar_List.hd b in fst uu____3256 in
                      (uu____3255, f1))
             | uu____3261 -> failwith "impossible" in
           (match uu____3224 with
            | (x,f) ->
                let uu____3268 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3268 with
                 | (base_t,decls) ->
                     let uu____3275 = gen_term_var env x in
                     (match uu____3275 with
                      | (x1,xtm,env') ->
                          let uu____3284 = encode_formula f env' in
                          (match uu____3284 with
                           | (refinement,decls') ->
                               let uu____3291 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3291 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3302 =
                                        let uu____3304 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3308 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3304
                                          uu____3308 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3302 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3324  ->
                                              match uu____3324 with
                                              | (y,uu____3328) ->
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
                                    let uu____3347 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3347 with
                                     | Some cache_entry ->
                                         let uu____3352 =
                                           let uu____3353 =
                                             let uu____3357 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3357) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3353 in
                                         (uu____3352,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3369 =
                                             let uu____3370 =
                                               let uu____3371 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3371 in
                                             Prims.strcat module_name
                                               uu____3370 in
                                           varops.mk_unique uu____3369 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3380 =
                                             let uu____3384 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3384) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3380 in
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
                                           let uu____3394 =
                                             let uu____3398 =
                                               let uu____3399 =
                                                 let uu____3405 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3405) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3399 in
                                             (uu____3398,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3394 in
                                         let t_kinding =
                                           let uu____3415 =
                                             let uu____3419 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3419,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3415 in
                                         let t_interp =
                                           let uu____3429 =
                                             let uu____3433 =
                                               let uu____3434 =
                                                 let uu____3440 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3440) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3434 in
                                             let uu____3452 =
                                               let uu____3454 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3454 in
                                             (uu____3433, uu____3452,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3429 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3459 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3459);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3476 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3476 in
           let uu____3477 = encode_term_pred None k env ttm in
           (match uu____3477 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3485 =
                    let uu____3489 =
                      let uu____3490 =
                        let uu____3491 =
                          let uu____3492 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3492 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3491 in
                      varops.mk_unique uu____3490 in
                    (t_has_k, (Some "Uvar typing"), uu____3489) in
                  FStar_SMTEncoding_Util.mkAssume uu____3485 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3495 ->
           let uu____3505 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3505 with
            | (head1,args_e) ->
                let uu____3533 =
                  let uu____3541 =
                    let uu____3542 = FStar_Syntax_Subst.compress head1 in
                    uu____3542.FStar_Syntax_Syntax.n in
                  (uu____3541, args_e) in
                (match uu____3533 with
                 | uu____3552 when head_redex env head1 ->
                     let uu____3560 = whnf env t in
                     encode_term uu____3560 env
                 | uu____3561 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____3574;
                       FStar_Syntax_Syntax.pos = uu____3575;
                       FStar_Syntax_Syntax.vars = uu____3576;_},uu____3577),uu____3578::
                    (v1,uu____3580)::(v2,uu____3582)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3620 = encode_term v1 env in
                     (match uu____3620 with
                      | (v11,decls1) ->
                          let uu____3627 = encode_term v2 env in
                          (match uu____3627 with
                           | (v21,decls2) ->
                               let uu____3634 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3634,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3637::(v1,uu____3639)::(v2,uu____3641)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3675 = encode_term v1 env in
                     (match uu____3675 with
                      | (v11,decls1) ->
                          let uu____3682 = encode_term v2 env in
                          (match uu____3682 with
                           | (v21,decls2) ->
                               let uu____3689 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3689,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3691) ->
                     let e0 =
                       let uu____3703 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3703 in
                     ((let uu____3709 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3709
                       then
                         let uu____3710 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3710
                       else ());
                      (let e =
                         let uu____3715 =
                           let uu____3716 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3717 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3716
                             uu____3717 in
                         uu____3715 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3726),(arg,uu____3728)::[]) -> encode_term arg env
                 | uu____3746 ->
                     let uu____3754 = encode_args args_e env in
                     (match uu____3754 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3787 = encode_term head1 env in
                            match uu____3787 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3826 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3826 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3868  ->
                                                 fun uu____3869  ->
                                                   match (uu____3868,
                                                           uu____3869)
                                                   with
                                                   | ((bv,uu____3883),
                                                      (a,uu____3885)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3899 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3899
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3904 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3904 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3914 =
                                                   let uu____3918 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3923 =
                                                     let uu____3924 =
                                                       let uu____3925 =
                                                         let uu____3926 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3926 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3925 in
                                                     varops.mk_unique
                                                       uu____3924 in
                                                   (uu____3918,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3923) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3914 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3943 = lookup_free_var_sym env fv in
                            match uu____3943 with
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
                                   FStar_Syntax_Syntax.tk = uu____3966;
                                   FStar_Syntax_Syntax.pos = uu____3967;
                                   FStar_Syntax_Syntax.vars = uu____3968;_},uu____3969)
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____3980;
                                   FStar_Syntax_Syntax.pos = uu____3981;
                                   FStar_Syntax_Syntax.vars = uu____3982;_},uu____3983)
                                ->
                                let uu____3988 =
                                  let uu____3989 =
                                    let uu____3992 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3992
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____3989
                                    FStar_Pervasives.snd in
                                Some uu____3988
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4012 =
                                  let uu____4013 =
                                    let uu____4016 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4016
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4013
                                    FStar_Pervasives.snd in
                                Some uu____4012
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4035,(FStar_Util.Inl t1,uu____4037),uu____4038)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4076,(FStar_Util.Inr c,uu____4078),uu____4079)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4117 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4137 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4137 in
                               let uu____4138 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4138 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4148;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4149;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4150;_},uu____4151)
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
                                     | uu____4175 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4220 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4220 with
            | (bs1,body1,opening) ->
                let fallback uu____4235 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____4240 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4240, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4251 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____4251
                  | FStar_Util.Inr (eff,uu____4253) ->
                      let uu____4259 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____4259 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4304 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___136_4305 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___136_4305.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___136_4305.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___136_4305.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___136_4305.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___136_4305.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___136_4305.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___136_4305.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___136_4305.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___136_4305.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___136_4305.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___136_4305.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___136_4305.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___136_4305.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___136_4305.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___136_4305.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___136_4305.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___136_4305.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___136_4305.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___136_4305.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___136_4305.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___136_4305.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___136_4305.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___136_4305.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4304 FStar_Syntax_Syntax.U_unknown in
                        let uu____4306 =
                          let uu____4307 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4307 in
                        FStar_Util.Inl uu____4306
                    | FStar_Util.Inr (eff_name,uu____4314) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4345 =
                        let uu____4346 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4346 in
                      FStar_All.pipe_right uu____4345
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4358 =
                        let uu____4359 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4359 FStar_Pervasives.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4367 =
                          let uu____4368 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4368 in
                        FStar_All.pipe_right uu____4367
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4372 =
                             let uu____4373 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4373 in
                           FStar_All.pipe_right uu____4372
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4384 =
                         let uu____4385 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4385 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4384);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4400 =
                       (is_impure lc1) &&
                         (let uu____4401 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4401) in
                     if uu____4400
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4406 = encode_binders None bs1 env in
                        match uu____4406 with
                        | (vars,guards,envbody,decls,uu____4421) ->
                            let uu____4428 =
                              let uu____4436 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4436
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4428 with
                             | (lc2,body2) ->
                                 let uu____4461 = encode_term body2 envbody in
                                 (match uu____4461 with
                                  | (body3,decls') ->
                                      let uu____4468 =
                                        let uu____4473 = codomain_eff lc2 in
                                        match uu____4473 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4485 =
                                              encode_term tfun env in
                                            (match uu____4485 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4468 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4504 =
                                               let uu____4510 =
                                                 let uu____4511 =
                                                   let uu____4514 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4514, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4511 in
                                               ([], vars, uu____4510) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4504 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4522 =
                                                   let uu____4524 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4524 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4522 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4535 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4535 with
                                            | Some cache_entry ->
                                                let uu____4540 =
                                                  let uu____4541 =
                                                    let uu____4545 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4545) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4541 in
                                                (uu____4540,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | None  ->
                                                let uu____4551 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4551 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4558 =
                                                         let uu____4559 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4559 =
                                                           cache_size in
                                                       if uu____4558
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
                                                         let uu____4570 =
                                                           let uu____4571 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4571 in
                                                         varops.mk_unique
                                                           uu____4570 in
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
                                                       let uu____4576 =
                                                         let uu____4580 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4580) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4576 in
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
                                                           let uu____4592 =
                                                             let uu____4593 =
                                                               let uu____4597
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4597,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4593 in
                                                           [uu____4592] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4605 =
                                                         let uu____4609 =
                                                           let uu____4610 =
                                                             let uu____4616 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4616) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4610 in
                                                         (uu____4609,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4605 in
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
                                                     ((let uu____4626 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4626);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4628,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4629;
                          FStar_Syntax_Syntax.lbunivs = uu____4630;
                          FStar_Syntax_Syntax.lbtyp = uu____4631;
                          FStar_Syntax_Syntax.lbeff = uu____4632;
                          FStar_Syntax_Syntax.lbdef = uu____4633;_}::uu____4634),uu____4635)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4653;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4655;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4671 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4684 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4684, [decl_e])))
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
              let uu____4726 = encode_term e1 env in
              match uu____4726 with
              | (ee1,decls1) ->
                  let uu____4733 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4733 with
                   | (xs,e21) ->
                       let uu____4747 = FStar_List.hd xs in
                       (match uu____4747 with
                        | (x1,uu____4755) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4757 = encode_body e21 env' in
                            (match uu____4757 with
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
            let uu____4779 =
              let uu____4783 =
                let uu____4784 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4784 in
              gen_term_var env uu____4783 in
            match uu____4779 with
            | (scrsym,scr',env1) ->
                let uu____4794 = encode_term e env1 in
                (match uu____4794 with
                 | (scr,decls) ->
                     let uu____4801 =
                       let encode_branch b uu____4817 =
                         match uu____4817 with
                         | (else_case,decls1) ->
                             let uu____4828 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4828 with
                              | (p,w,br) ->
                                  let uu____4849 = encode_pat env1 p in
                                  (match uu____4849 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____4869  ->
                                                   match uu____4869 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____4874 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____4889 =
                                               encode_term w1 env2 in
                                             (match uu____4889 with
                                              | (w2,decls2) ->
                                                  let uu____4897 =
                                                    let uu____4898 =
                                                      let uu____4901 =
                                                        let uu____4902 =
                                                          let uu____4905 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____4905) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____4902 in
                                                      (guard, uu____4901) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____4898 in
                                                  (uu____4897, decls2)) in
                                       (match uu____4874 with
                                        | (guard1,decls2) ->
                                            let uu____4913 =
                                              encode_br br env2 in
                                            (match uu____4913 with
                                             | (br1,decls3) ->
                                                 let uu____4921 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____4921,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4801 with
                      | (match_tm,decls1) ->
                          let uu____4932 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4932, decls1)))
and encode_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4954 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4954
       then
         let uu____4955 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4955
       else ());
      (let uu____4957 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4957 with
       | (vars,pat_term) ->
           let uu____4967 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4990  ->
                     fun v1  ->
                       match uu____4990 with
                       | (env1,vars1) ->
                           let uu____5018 = gen_term_var env1 v1 in
                           (match uu____5018 with
                            | (xx,uu____5030,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4967 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5077 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5078 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5079 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5085 =
                        let uu____5088 = encode_const c in
                        (scrutinee, uu____5088) in
                      FStar_SMTEncoding_Util.mkEq uu____5085
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5107 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5107 with
                        | (uu____5111,uu____5112::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5114 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5135  ->
                                  match uu____5135 with
                                  | (arg,uu____5141) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5151 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5151)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5171) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5190 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5205 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5227  ->
                                  match uu____5227 with
                                  | (arg,uu____5236) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5246 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5246)) in
                      FStar_All.pipe_right uu____5205 FStar_List.flatten in
                let pat_term1 uu____5262 = encode_term pat_term env1 in
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
      let uu____5269 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5284  ->
                fun uu____5285  ->
                  match (uu____5284, uu____5285) with
                  | ((tms,decls),(t,uu____5305)) ->
                      let uu____5316 = encode_term t env in
                      (match uu____5316 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5269 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5350 = FStar_Syntax_Util.list_elements e in
        match uu____5350 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5368 =
          let uu____5378 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5378 FStar_Syntax_Util.head_and_args in
        match uu____5368 with
        | (head1,args) ->
            let uu____5409 =
              let uu____5417 =
                let uu____5418 = FStar_Syntax_Util.un_uinst head1 in
                uu____5418.FStar_Syntax_Syntax.n in
              (uu____5417, args) in
            (match uu____5409 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5432,uu____5433)::(e,uu____5435)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> (e, None)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5466)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpatT_lid
                 -> (e, None)
             | uu____5487 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or t1 =
          let uu____5520 =
            let uu____5530 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5530 FStar_Syntax_Util.head_and_args in
          match uu____5520 with
          | (head1,args) ->
              let uu____5559 =
                let uu____5567 =
                  let uu____5568 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5568.FStar_Syntax_Syntax.n in
                (uu____5567, args) in
              (match uu____5559 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5581)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5601 -> None) in
        match elts with
        | t1::[] ->
            let uu____5619 = smt_pat_or t1 in
            (match uu____5619 with
             | Some e ->
                 let uu____5635 = list_elements1 e in
                 FStar_All.pipe_right uu____5635
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5652 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5652
                           (FStar_List.map one_pat)))
             | uu____5666 ->
                 let uu____5670 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5670])
        | uu____5701 ->
            let uu____5703 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5703] in
      let uu____5734 =
        let uu____5750 =
          let uu____5751 = FStar_Syntax_Subst.compress t in
          uu____5751.FStar_Syntax_Syntax.n in
        match uu____5750 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5781 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5781 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5816;
                        FStar_Syntax_Syntax.effect_name = uu____5817;
                        FStar_Syntax_Syntax.result_typ = uu____5818;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5820)::(post,uu____5822)::(pats,uu____5824)::[];
                        FStar_Syntax_Syntax.flags = uu____5825;_}
                      ->
                      let uu____5857 = lemma_pats pats in
                      (binders1, pre, post, uu____5857)
                  | uu____5876 -> failwith "impos"))
        | uu____5892 -> failwith "Impos" in
      match uu____5734 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___137_5937 = env in
            {
              bindings = (uu___137_5937.bindings);
              depth = (uu___137_5937.depth);
              tcenv = (uu___137_5937.tcenv);
              warn = (uu___137_5937.warn);
              cache = (uu___137_5937.cache);
              nolabels = (uu___137_5937.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___137_5937.encode_non_total_function_typ);
              current_module_name = (uu___137_5937.current_module_name)
            } in
          let uu____5938 = encode_binders None binders env1 in
          (match uu____5938 with
           | (vars,guards,env2,decls,uu____5953) ->
               let uu____5960 =
                 let uu____5967 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____5998 =
                             let uu____6003 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun uu____6019  ->
                                       match uu____6019 with
                                       | (t1,uu____6026) ->
                                           encode_term t1 env2)) in
                             FStar_All.pipe_right uu____6003 FStar_List.unzip in
                           match uu____5998 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____5967 FStar_List.unzip in
               (match uu____5960 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___138_6076 = env2 in
                      {
                        bindings = (uu___138_6076.bindings);
                        depth = (uu___138_6076.depth);
                        tcenv = (uu___138_6076.tcenv);
                        warn = (uu___138_6076.warn);
                        cache = (uu___138_6076.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___138_6076.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___138_6076.encode_non_total_function_typ);
                        current_module_name =
                          (uu___138_6076.current_module_name)
                      } in
                    let uu____6077 =
                      let uu____6080 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6080 env3 in
                    (match uu____6077 with
                     | (pre1,decls'') ->
                         let uu____6085 =
                           let uu____6088 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6088 env3 in
                         (match uu____6085 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6095 =
                                let uu____6096 =
                                  let uu____6102 =
                                    let uu____6103 =
                                      let uu____6106 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6106, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6103 in
                                  (pats, vars, uu____6102) in
                                FStar_SMTEncoding_Util.mkForall uu____6096 in
                              (uu____6095, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6119 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6119
        then
          let uu____6120 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6121 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6120 uu____6121
        else () in
      let enc f r l =
        let uu____6148 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6161 = encode_term (fst x) env in
                 match uu____6161 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6148 with
        | (decls,args) ->
            let uu____6178 =
              let uu___139_6179 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6179.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6179.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6178, decls) in
      let const_op f r uu____6198 = let uu____6201 = f r in (uu____6201, []) in
      let un_op f l =
        let uu____6217 = FStar_List.hd l in FStar_All.pipe_left f uu____6217 in
      let bin_op f uu___111_6230 =
        match uu___111_6230 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6238 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6265 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6274  ->
                 match uu____6274 with
                 | (t,uu____6282) ->
                     let uu____6283 = encode_formula t env in
                     (match uu____6283 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6265 with
        | (decls,phis) ->
            let uu____6300 =
              let uu___140_6301 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_6301.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_6301.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6300, decls) in
      let eq_op r uu___112_6317 =
        match uu___112_6317 with
        | uu____6320::e1::e2::[] ->
            let uu____6351 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6351 r [e1; e2]
        | uu____6370::uu____6371::e1::e2::[] ->
            let uu____6410 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6410 r [e1; e2]
        | l ->
            let uu____6430 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6430 r l in
      let mk_imp1 r uu___113_6449 =
        match uu___113_6449 with
        | (lhs,uu____6453)::(rhs,uu____6455)::[] ->
            let uu____6476 = encode_formula rhs env in
            (match uu____6476 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6485) ->
                      (l1, decls1)
                  | uu____6488 ->
                      let uu____6489 = encode_formula lhs env in
                      (match uu____6489 with
                       | (l2,decls2) ->
                           let uu____6496 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6496, (FStar_List.append decls1 decls2)))))
        | uu____6498 -> failwith "impossible" in
      let mk_ite r uu___114_6513 =
        match uu___114_6513 with
        | (guard,uu____6517)::(_then,uu____6519)::(_else,uu____6521)::[] ->
            let uu____6550 = encode_formula guard env in
            (match uu____6550 with
             | (g,decls1) ->
                 let uu____6557 = encode_formula _then env in
                 (match uu____6557 with
                  | (t,decls2) ->
                      let uu____6564 = encode_formula _else env in
                      (match uu____6564 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6573 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6592 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6592 in
      let connectives =
        let uu____6604 =
          let uu____6613 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6613) in
        let uu____6626 =
          let uu____6636 =
            let uu____6645 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6645) in
          let uu____6658 =
            let uu____6668 =
              let uu____6678 =
                let uu____6687 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6687) in
              let uu____6700 =
                let uu____6710 =
                  let uu____6720 =
                    let uu____6729 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6729) in
                  [uu____6720;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6710 in
              uu____6678 :: uu____6700 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6668 in
          uu____6636 :: uu____6658 in
        uu____6604 :: uu____6626 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6891 = encode_formula phi' env in
            (match uu____6891 with
             | (phi2,decls) ->
                 let uu____6898 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6898, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6899 ->
            let uu____6904 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6904 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6933 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6933 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6941;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6943;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6959 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6959 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6991::(x,uu____6993)::(t,uu____6995)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____7029 = encode_term x env in
                 (match uu____7029 with
                  | (x1,decls) ->
                      let uu____7036 = encode_term t env in
                      (match uu____7036 with
                       | (t1,decls') ->
                           let uu____7043 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____7043, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____7047)::(msg,uu____7049)::(phi2,uu____7051)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____7085 =
                   let uu____7088 =
                     let uu____7089 = FStar_Syntax_Subst.compress r in
                     uu____7089.FStar_Syntax_Syntax.n in
                   let uu____7092 =
                     let uu____7093 = FStar_Syntax_Subst.compress msg in
                     uu____7093.FStar_Syntax_Syntax.n in
                   (uu____7088, uu____7092) in
                 (match uu____7085 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7100))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____7116 -> fallback phi2)
             | uu____7119 when head_redex env head2 ->
                 let uu____7127 = whnf env phi1 in
                 encode_formula uu____7127 env
             | uu____7128 ->
                 let uu____7136 = encode_term phi1 env in
                 (match uu____7136 with
                  | (tt,decls) ->
                      let uu____7143 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___141_7144 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___141_7144.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___141_7144.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7143, decls)))
        | uu____7147 ->
            let uu____7148 = encode_term phi1 env in
            (match uu____7148 with
             | (tt,decls) ->
                 let uu____7155 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___142_7156 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___142_7156.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___142_7156.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7155, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7183 = encode_binders None bs env1 in
        match uu____7183 with
        | (vars,guards,env2,decls,uu____7205) ->
            let uu____7212 =
              let uu____7219 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7242 =
                          let uu____7247 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7261  ->
                                    match uu____7261 with
                                    | (t,uu____7267) ->
                                        encode_term t
                                          (let uu___143_7268 = env2 in
                                           {
                                             bindings =
                                               (uu___143_7268.bindings);
                                             depth = (uu___143_7268.depth);
                                             tcenv = (uu___143_7268.tcenv);
                                             warn = (uu___143_7268.warn);
                                             cache = (uu___143_7268.cache);
                                             nolabels =
                                               (uu___143_7268.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___143_7268.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___143_7268.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7247 FStar_List.unzip in
                        match uu____7242 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7219 FStar_List.unzip in
            (match uu____7212 with
             | (pats,decls') ->
                 let uu____7320 = encode_formula body env2 in
                 (match uu____7320 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7339;
                             FStar_SMTEncoding_Term.rng = uu____7340;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7348 -> guards in
                      let uu____7351 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7351, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7385  ->
                   match uu____7385 with
                   | (x,uu____7389) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7395 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7401 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7401) uu____7395 tl1 in
             let uu____7403 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7415  ->
                       match uu____7415 with
                       | (b,uu____7419) ->
                           let uu____7420 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7420)) in
             (match uu____7403 with
              | None  -> ()
              | Some (x,uu____7424) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7434 =
                    let uu____7435 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7435 in
                  FStar_Errors.warn pos uu____7434) in
       let uu____7436 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7436 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7442 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7478  ->
                     match uu____7478 with
                     | (l,uu____7488) -> FStar_Ident.lid_equals op l)) in
           (match uu____7442 with
            | None  -> fallback phi1
            | Some (uu____7511,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7540 = encode_q_body env vars pats body in
             match uu____7540 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7566 =
                     let uu____7572 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7572) in
                   FStar_SMTEncoding_Term.mkForall uu____7566
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7584 = encode_q_body env vars pats body in
             match uu____7584 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7609 =
                   let uu____7610 =
                     let uu____7616 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7616) in
                   FStar_SMTEncoding_Term.mkExists uu____7610
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7609, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7665 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7665 with
  | (asym,a) ->
      let uu____7670 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7670 with
       | (xsym,x) ->
           let uu____7675 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7675 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7705 =
                      let uu____7711 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____7711, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7705 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7726 =
                      let uu____7730 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7730) in
                    FStar_SMTEncoding_Util.mkApp uu____7726 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7738 =
                    let uu____7740 =
                      let uu____7742 =
                        let uu____7744 =
                          let uu____7745 =
                            let uu____7749 =
                              let uu____7750 =
                                let uu____7756 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7756) in
                              FStar_SMTEncoding_Util.mkForall uu____7750 in
                            (uu____7749, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7745 in
                        let uu____7765 =
                          let uu____7767 =
                            let uu____7768 =
                              let uu____7772 =
                                let uu____7773 =
                                  let uu____7779 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7779) in
                                FStar_SMTEncoding_Util.mkForall uu____7773 in
                              (uu____7772,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7768 in
                          [uu____7767] in
                        uu____7744 :: uu____7765 in
                      xtok_decl :: uu____7742 in
                    xname_decl :: uu____7740 in
                  (xtok1, uu____7738) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7828 =
                    let uu____7836 =
                      let uu____7842 =
                        let uu____7843 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7843 in
                      quant axy uu____7842 in
                    (FStar_Syntax_Const.op_Eq, uu____7836) in
                  let uu____7849 =
                    let uu____7858 =
                      let uu____7866 =
                        let uu____7872 =
                          let uu____7873 =
                            let uu____7874 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7874 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7873 in
                        quant axy uu____7872 in
                      (FStar_Syntax_Const.op_notEq, uu____7866) in
                    let uu____7880 =
                      let uu____7889 =
                        let uu____7897 =
                          let uu____7903 =
                            let uu____7904 =
                              let uu____7905 =
                                let uu____7908 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7909 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7908, uu____7909) in
                              FStar_SMTEncoding_Util.mkLT uu____7905 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7904 in
                          quant xy uu____7903 in
                        (FStar_Syntax_Const.op_LT, uu____7897) in
                      let uu____7915 =
                        let uu____7924 =
                          let uu____7932 =
                            let uu____7938 =
                              let uu____7939 =
                                let uu____7940 =
                                  let uu____7943 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7944 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7943, uu____7944) in
                                FStar_SMTEncoding_Util.mkLTE uu____7940 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7939 in
                            quant xy uu____7938 in
                          (FStar_Syntax_Const.op_LTE, uu____7932) in
                        let uu____7950 =
                          let uu____7959 =
                            let uu____7967 =
                              let uu____7973 =
                                let uu____7974 =
                                  let uu____7975 =
                                    let uu____7978 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7979 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7978, uu____7979) in
                                  FStar_SMTEncoding_Util.mkGT uu____7975 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7974 in
                              quant xy uu____7973 in
                            (FStar_Syntax_Const.op_GT, uu____7967) in
                          let uu____7985 =
                            let uu____7994 =
                              let uu____8002 =
                                let uu____8008 =
                                  let uu____8009 =
                                    let uu____8010 =
                                      let uu____8013 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____8014 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____8013, uu____8014) in
                                    FStar_SMTEncoding_Util.mkGTE uu____8010 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____8009 in
                                quant xy uu____8008 in
                              (FStar_Syntax_Const.op_GTE, uu____8002) in
                            let uu____8020 =
                              let uu____8029 =
                                let uu____8037 =
                                  let uu____8043 =
                                    let uu____8044 =
                                      let uu____8045 =
                                        let uu____8048 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____8049 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____8048, uu____8049) in
                                      FStar_SMTEncoding_Util.mkSub uu____8045 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8044 in
                                  quant xy uu____8043 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____8037) in
                              let uu____8055 =
                                let uu____8064 =
                                  let uu____8072 =
                                    let uu____8078 =
                                      let uu____8079 =
                                        let uu____8080 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8080 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8079 in
                                    quant qx uu____8078 in
                                  (FStar_Syntax_Const.op_Minus, uu____8072) in
                                let uu____8086 =
                                  let uu____8095 =
                                    let uu____8103 =
                                      let uu____8109 =
                                        let uu____8110 =
                                          let uu____8111 =
                                            let uu____8114 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8115 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8114, uu____8115) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8111 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8110 in
                                      quant xy uu____8109 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8103) in
                                  let uu____8121 =
                                    let uu____8130 =
                                      let uu____8138 =
                                        let uu____8144 =
                                          let uu____8145 =
                                            let uu____8146 =
                                              let uu____8149 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8150 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8149, uu____8150) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8146 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8145 in
                                        quant xy uu____8144 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8138) in
                                    let uu____8156 =
                                      let uu____8165 =
                                        let uu____8173 =
                                          let uu____8179 =
                                            let uu____8180 =
                                              let uu____8181 =
                                                let uu____8184 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8185 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8184, uu____8185) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8181 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8180 in
                                          quant xy uu____8179 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8173) in
                                      let uu____8191 =
                                        let uu____8200 =
                                          let uu____8208 =
                                            let uu____8214 =
                                              let uu____8215 =
                                                let uu____8216 =
                                                  let uu____8219 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8220 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8219, uu____8220) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8216 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8215 in
                                            quant xy uu____8214 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8208) in
                                        let uu____8226 =
                                          let uu____8235 =
                                            let uu____8243 =
                                              let uu____8249 =
                                                let uu____8250 =
                                                  let uu____8251 =
                                                    let uu____8254 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8255 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8254, uu____8255) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8251 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8250 in
                                              quant xy uu____8249 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8243) in
                                          let uu____8261 =
                                            let uu____8270 =
                                              let uu____8278 =
                                                let uu____8284 =
                                                  let uu____8285 =
                                                    let uu____8286 =
                                                      let uu____8289 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8290 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8289,
                                                        uu____8290) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8286 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8285 in
                                                quant xy uu____8284 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8278) in
                                            let uu____8296 =
                                              let uu____8305 =
                                                let uu____8313 =
                                                  let uu____8319 =
                                                    let uu____8320 =
                                                      let uu____8321 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8321 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8320 in
                                                  quant qx uu____8319 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8313) in
                                              [uu____8305] in
                                            uu____8270 :: uu____8296 in
                                          uu____8235 :: uu____8261 in
                                        uu____8200 :: uu____8226 in
                                      uu____8165 :: uu____8191 in
                                    uu____8130 :: uu____8156 in
                                  uu____8095 :: uu____8121 in
                                uu____8064 :: uu____8086 in
                              uu____8029 :: uu____8055 in
                            uu____7994 :: uu____8020 in
                          uu____7959 :: uu____7985 in
                        uu____7924 :: uu____7950 in
                      uu____7889 :: uu____7915 in
                    uu____7858 :: uu____7880 in
                  uu____7828 :: uu____7849 in
                let mk1 l v1 =
                  let uu____8449 =
                    let uu____8454 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8486  ->
                              match uu____8486 with
                              | (l',uu____8495) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8454
                      (FStar_Option.map
                         (fun uu____8528  ->
                            match uu____8528 with | (uu____8539,b) -> b v1)) in
                  FStar_All.pipe_right uu____8449 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8580  ->
                          match uu____8580 with
                          | (l',uu____8589) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8615 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8615 with
        | (xxsym,xx) ->
            let uu____8620 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8620 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8628 =
                   let uu____8632 =
                     let uu____8633 =
                       let uu____8639 =
                         let uu____8640 =
                           let uu____8643 =
                             let uu____8644 =
                               let uu____8647 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8647) in
                             FStar_SMTEncoding_Util.mkEq uu____8644 in
                           (xx_has_type, uu____8643) in
                         FStar_SMTEncoding_Util.mkImp uu____8640 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8639) in
                     FStar_SMTEncoding_Util.mkForall uu____8633 in
                   let uu____8660 =
                     let uu____8661 =
                       let uu____8662 =
                         let uu____8663 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8663 in
                       Prims.strcat module_name uu____8662 in
                     varops.mk_unique uu____8661 in
                   (uu____8632, (Some "pretyping"), uu____8660) in
                 FStar_SMTEncoding_Util.mkAssume uu____8628)
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
    let uu____8693 =
      let uu____8694 =
        let uu____8698 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8698, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8694 in
    let uu____8700 =
      let uu____8702 =
        let uu____8703 =
          let uu____8707 =
            let uu____8708 =
              let uu____8714 =
                let uu____8715 =
                  let uu____8718 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8718) in
                FStar_SMTEncoding_Util.mkImp uu____8715 in
              ([[typing_pred]], [xx], uu____8714) in
            mkForall_fuel uu____8708 in
          (uu____8707, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8703 in
      [uu____8702] in
    uu____8693 :: uu____8700 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8746 =
      let uu____8747 =
        let uu____8751 =
          let uu____8752 =
            let uu____8758 =
              let uu____8761 =
                let uu____8763 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8763] in
              [uu____8761] in
            let uu____8766 =
              let uu____8767 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8767 tt in
            (uu____8758, [bb], uu____8766) in
          FStar_SMTEncoding_Util.mkForall uu____8752 in
        (uu____8751, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8747 in
    let uu____8778 =
      let uu____8780 =
        let uu____8781 =
          let uu____8785 =
            let uu____8786 =
              let uu____8792 =
                let uu____8793 =
                  let uu____8796 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8796) in
                FStar_SMTEncoding_Util.mkImp uu____8793 in
              ([[typing_pred]], [xx], uu____8792) in
            mkForall_fuel uu____8786 in
          (uu____8785, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8781 in
      [uu____8780] in
    uu____8746 :: uu____8778 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8830 =
        let uu____8831 =
          let uu____8835 =
            let uu____8837 =
              let uu____8839 =
                let uu____8841 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8842 =
                  let uu____8844 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8844] in
                uu____8841 :: uu____8842 in
              tt :: uu____8839 in
            tt :: uu____8837 in
          ("Prims.Precedes", uu____8835) in
        FStar_SMTEncoding_Util.mkApp uu____8831 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8830 in
    let precedes_y_x =
      let uu____8847 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8847 in
    let uu____8849 =
      let uu____8850 =
        let uu____8854 =
          let uu____8855 =
            let uu____8861 =
              let uu____8864 =
                let uu____8866 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8866] in
              [uu____8864] in
            let uu____8869 =
              let uu____8870 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8870 tt in
            (uu____8861, [bb], uu____8869) in
          FStar_SMTEncoding_Util.mkForall uu____8855 in
        (uu____8854, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8850 in
    let uu____8881 =
      let uu____8883 =
        let uu____8884 =
          let uu____8888 =
            let uu____8889 =
              let uu____8895 =
                let uu____8896 =
                  let uu____8899 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8899) in
                FStar_SMTEncoding_Util.mkImp uu____8896 in
              ([[typing_pred]], [xx], uu____8895) in
            mkForall_fuel uu____8889 in
          (uu____8888, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8884 in
      let uu____8912 =
        let uu____8914 =
          let uu____8915 =
            let uu____8919 =
              let uu____8920 =
                let uu____8926 =
                  let uu____8927 =
                    let uu____8930 =
                      let uu____8931 =
                        let uu____8933 =
                          let uu____8935 =
                            let uu____8937 =
                              let uu____8938 =
                                let uu____8941 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8942 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8941, uu____8942) in
                              FStar_SMTEncoding_Util.mkGT uu____8938 in
                            let uu____8943 =
                              let uu____8945 =
                                let uu____8946 =
                                  let uu____8949 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8950 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8949, uu____8950) in
                                FStar_SMTEncoding_Util.mkGTE uu____8946 in
                              let uu____8951 =
                                let uu____8953 =
                                  let uu____8954 =
                                    let uu____8957 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8958 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8957, uu____8958) in
                                  FStar_SMTEncoding_Util.mkLT uu____8954 in
                                [uu____8953] in
                              uu____8945 :: uu____8951 in
                            uu____8937 :: uu____8943 in
                          typing_pred_y :: uu____8935 in
                        typing_pred :: uu____8933 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8931 in
                    (uu____8930, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8927 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8926) in
              mkForall_fuel uu____8920 in
            (uu____8919, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8915 in
        [uu____8914] in
      uu____8883 :: uu____8912 in
    uu____8849 :: uu____8881 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8988 =
      let uu____8989 =
        let uu____8993 =
          let uu____8994 =
            let uu____9000 =
              let uu____9003 =
                let uu____9005 = FStar_SMTEncoding_Term.boxString b in
                [uu____9005] in
              [uu____9003] in
            let uu____9008 =
              let uu____9009 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____9009 tt in
            (uu____9000, [bb], uu____9008) in
          FStar_SMTEncoding_Util.mkForall uu____8994 in
        (uu____8993, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8989 in
    let uu____9020 =
      let uu____9022 =
        let uu____9023 =
          let uu____9027 =
            let uu____9028 =
              let uu____9034 =
                let uu____9035 =
                  let uu____9038 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____9038) in
                FStar_SMTEncoding_Util.mkImp uu____9035 in
              ([[typing_pred]], [xx], uu____9034) in
            mkForall_fuel uu____9028 in
          (uu____9027, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9023 in
      [uu____9022] in
    uu____8988 :: uu____9020 in
  let mk_ref1 env reft_name uu____9060 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____9071 =
        let uu____9075 =
          let uu____9077 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9077] in
        (reft_name, uu____9075) in
      FStar_SMTEncoding_Util.mkApp uu____9071 in
    let refb =
      let uu____9080 =
        let uu____9084 =
          let uu____9086 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9086] in
        (reft_name, uu____9084) in
      FStar_SMTEncoding_Util.mkApp uu____9080 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9090 =
      let uu____9091 =
        let uu____9095 =
          let uu____9096 =
            let uu____9102 =
              let uu____9103 =
                let uu____9106 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9106) in
              FStar_SMTEncoding_Util.mkImp uu____9103 in
            ([[typing_pred]], [xx; aa], uu____9102) in
          mkForall_fuel uu____9096 in
        (uu____9095, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9091 in
    [uu____9090] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9146 =
      let uu____9147 =
        let uu____9151 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9151, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9147 in
    [uu____9146] in
  let mk_and_interp env conj uu____9162 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9179 =
      let uu____9180 =
        let uu____9184 =
          let uu____9185 =
            let uu____9191 =
              let uu____9192 =
                let uu____9195 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9195, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9192 in
            ([[l_and_a_b]], [aa; bb], uu____9191) in
          FStar_SMTEncoding_Util.mkForall uu____9185 in
        (uu____9184, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9180 in
    [uu____9179] in
  let mk_or_interp env disj uu____9219 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9236 =
      let uu____9237 =
        let uu____9241 =
          let uu____9242 =
            let uu____9248 =
              let uu____9249 =
                let uu____9252 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9252, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9249 in
            ([[l_or_a_b]], [aa; bb], uu____9248) in
          FStar_SMTEncoding_Util.mkForall uu____9242 in
        (uu____9241, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9237 in
    [uu____9236] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9293 =
      let uu____9294 =
        let uu____9298 =
          let uu____9299 =
            let uu____9305 =
              let uu____9306 =
                let uu____9309 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9309, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9306 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9305) in
          FStar_SMTEncoding_Util.mkForall uu____9299 in
        (uu____9298, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9294 in
    [uu____9293] in
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
    let uu____9356 =
      let uu____9357 =
        let uu____9361 =
          let uu____9362 =
            let uu____9368 =
              let uu____9369 =
                let uu____9372 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9372, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9369 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9368) in
          FStar_SMTEncoding_Util.mkForall uu____9362 in
        (uu____9361, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9357 in
    [uu____9356] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9417 =
      let uu____9418 =
        let uu____9422 =
          let uu____9423 =
            let uu____9429 =
              let uu____9430 =
                let uu____9433 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9433, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9430 in
            ([[l_imp_a_b]], [aa; bb], uu____9429) in
          FStar_SMTEncoding_Util.mkForall uu____9423 in
        (uu____9422, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9418 in
    [uu____9417] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9474 =
      let uu____9475 =
        let uu____9479 =
          let uu____9480 =
            let uu____9486 =
              let uu____9487 =
                let uu____9490 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9490, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9487 in
            ([[l_iff_a_b]], [aa; bb], uu____9486) in
          FStar_SMTEncoding_Util.mkForall uu____9480 in
        (uu____9479, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9475 in
    [uu____9474] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9524 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9524 in
    let uu____9526 =
      let uu____9527 =
        let uu____9531 =
          let uu____9532 =
            let uu____9538 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9538) in
          FStar_SMTEncoding_Util.mkForall uu____9532 in
        (uu____9531, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9527 in
    [uu____9526] in
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
      let uu____9578 =
        let uu____9582 =
          let uu____9584 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9584] in
        ("Valid", uu____9582) in
      FStar_SMTEncoding_Util.mkApp uu____9578 in
    let uu____9586 =
      let uu____9587 =
        let uu____9591 =
          let uu____9592 =
            let uu____9598 =
              let uu____9599 =
                let uu____9602 =
                  let uu____9603 =
                    let uu____9609 =
                      let uu____9612 =
                        let uu____9614 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9614] in
                      [uu____9612] in
                    let uu____9617 =
                      let uu____9618 =
                        let uu____9621 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9621, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9618 in
                    (uu____9609, [xx1], uu____9617) in
                  FStar_SMTEncoding_Util.mkForall uu____9603 in
                (uu____9602, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9599 in
            ([[l_forall_a_b]], [aa; bb], uu____9598) in
          FStar_SMTEncoding_Util.mkForall uu____9592 in
        (uu____9591, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9587 in
    [uu____9586] in
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
      let uu____9672 =
        let uu____9676 =
          let uu____9678 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9678] in
        ("Valid", uu____9676) in
      FStar_SMTEncoding_Util.mkApp uu____9672 in
    let uu____9680 =
      let uu____9681 =
        let uu____9685 =
          let uu____9686 =
            let uu____9692 =
              let uu____9693 =
                let uu____9696 =
                  let uu____9697 =
                    let uu____9703 =
                      let uu____9706 =
                        let uu____9708 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9708] in
                      [uu____9706] in
                    let uu____9711 =
                      let uu____9712 =
                        let uu____9715 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9715, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9712 in
                    (uu____9703, [xx1], uu____9711) in
                  FStar_SMTEncoding_Util.mkExists uu____9697 in
                (uu____9696, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9693 in
            ([[l_exists_a_b]], [aa; bb], uu____9692) in
          FStar_SMTEncoding_Util.mkForall uu____9686 in
        (uu____9685, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9681 in
    [uu____9680] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9751 =
      let uu____9752 =
        let uu____9756 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9757 = varops.mk_unique "typing_range_const" in
        (uu____9756, (Some "Range_const typing"), uu____9757) in
      FStar_SMTEncoding_Util.mkAssume uu____9752 in
    [uu____9751] in
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
          let uu____10019 =
            FStar_Util.find_opt
              (fun uu____10037  ->
                 match uu____10037 with
                 | (l,uu____10047) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____10019 with
          | None  -> []
          | Some (uu____10069,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10106 = encode_function_type_as_formula t env in
        match uu____10106 with
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
            let uu____10138 =
              (let uu____10139 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10139) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10138
            then
              let uu____10143 = new_term_constant_and_tok_from_lid env lid in
              match uu____10143 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10155 =
                      let uu____10156 = FStar_Syntax_Subst.compress t_norm in
                      uu____10156.FStar_Syntax_Syntax.n in
                    match uu____10155 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10161) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10178  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10181 -> [] in
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
              (let uu____10190 = prims.is lid in
               if uu____10190
               then
                 let vname = varops.new_fvar lid in
                 let uu____10195 = prims.mk lid vname in
                 match uu____10195 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10210 =
                    let uu____10216 = curried_arrow_formals_comp t_norm in
                    match uu____10216 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10227 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10227
                          then
                            let uu____10228 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___144_10229 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___144_10229.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___144_10229.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___144_10229.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___144_10229.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___144_10229.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___144_10229.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___144_10229.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___144_10229.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___144_10229.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___144_10229.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___144_10229.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___144_10229.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___144_10229.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___144_10229.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___144_10229.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___144_10229.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___144_10229.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___144_10229.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___144_10229.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___144_10229.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___144_10229.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___144_10229.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___144_10229.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10228
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10236 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10236)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10210 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10263 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10263 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10276 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10300  ->
                                     match uu___115_10300 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10303 =
                                           FStar_Util.prefix vars in
                                         (match uu____10303 with
                                          | (uu____10314,(xxsym,uu____10316))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10326 =
                                                let uu____10327 =
                                                  let uu____10331 =
                                                    let uu____10332 =
                                                      let uu____10338 =
                                                        let uu____10339 =
                                                          let uu____10342 =
                                                            let uu____10343 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10343 in
                                                          (vapp, uu____10342) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10339 in
                                                      ([[vapp]], vars,
                                                        uu____10338) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10332 in
                                                  (uu____10331,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10327 in
                                              [uu____10326])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10354 =
                                           FStar_Util.prefix vars in
                                         (match uu____10354 with
                                          | (uu____10365,(xxsym,uu____10367))
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
                                              let uu____10381 =
                                                let uu____10382 =
                                                  let uu____10386 =
                                                    let uu____10387 =
                                                      let uu____10393 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10393) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10387 in
                                                  (uu____10386,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10382 in
                                              [uu____10381])
                                     | uu____10402 -> [])) in
                           let uu____10403 = encode_binders None formals env1 in
                           (match uu____10403 with
                            | (vars,guards,env',decls1,uu____10419) ->
                                let uu____10426 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10431 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10431, decls1)
                                  | Some p ->
                                      let uu____10433 = encode_formula p env' in
                                      (match uu____10433 with
                                       | (g,ds) ->
                                           let uu____10440 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10440,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10426 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10449 =
                                         let uu____10453 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10453) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10449 in
                                     let uu____10458 =
                                       let vname_decl =
                                         let uu____10463 =
                                           let uu____10469 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10474  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10469,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10463 in
                                       let uu____10479 =
                                         let env2 =
                                           let uu___145_10483 = env1 in
                                           {
                                             bindings =
                                               (uu___145_10483.bindings);
                                             depth = (uu___145_10483.depth);
                                             tcenv = (uu___145_10483.tcenv);
                                             warn = (uu___145_10483.warn);
                                             cache = (uu___145_10483.cache);
                                             nolabels =
                                               (uu___145_10483.nolabels);
                                             use_zfuel_name =
                                               (uu___145_10483.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___145_10483.current_module_name)
                                           } in
                                         let uu____10484 =
                                           let uu____10485 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10485 in
                                         if uu____10484
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10479 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10495::uu____10496 ->
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
                                                   let uu____10519 =
                                                     let uu____10525 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10525) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10519 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10539 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10541 =
                                             match formals with
                                             | [] ->
                                                 let uu____10550 =
                                                   let uu____10551 =
                                                     let uu____10553 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10553 in
                                                   push_free_var env1 lid
                                                     vname uu____10551 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10550)
                                             | uu____10556 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10561 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10561 in
                                                 let name_tok_corr =
                                                   let uu____10563 =
                                                     let uu____10567 =
                                                       let uu____10568 =
                                                         let uu____10574 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10574) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10568 in
                                                     (uu____10567,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10563 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10541 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10458 with
                                      | (decls2,env2) ->
                                          let uu____10598 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10603 =
                                              encode_term res_t1 env' in
                                            match uu____10603 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10611 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10611,
                                                  decls) in
                                          (match uu____10598 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10619 =
                                                   let uu____10623 =
                                                     let uu____10624 =
                                                       let uu____10630 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10630) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10624 in
                                                   (uu____10623,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10619 in
                                               let freshness =
                                                 let uu____10639 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10639
                                                 then
                                                   let uu____10642 =
                                                     let uu____10643 =
                                                       let uu____10649 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
                                                       let uu____10655 =
                                                         varops.next_id () in
                                                       (vname, uu____10649,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10655) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10643 in
                                                   let uu____10657 =
                                                     let uu____10659 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10659] in
                                                   uu____10642 :: uu____10657
                                                 else [] in
                                               let g =
                                                 let uu____10663 =
                                                   let uu____10665 =
                                                     let uu____10667 =
                                                       let uu____10669 =
                                                         let uu____10671 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10671 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10669 in
                                                     FStar_List.append decls3
                                                       uu____10667 in
                                                   FStar_List.append decls2
                                                     uu____10665 in
                                                 FStar_List.append decls11
                                                   uu____10663 in
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
          let uu____10693 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10693 with
          | None  ->
              let uu____10716 = encode_free_var env x t t_norm [] in
              (match uu____10716 with
               | (decls,env1) ->
                   let uu____10731 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10731 with
                    | (n1,x',uu____10750) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10762) -> ((n1, x1), [], env)
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
          let uu____10795 = encode_free_var env lid t tt quals in
          match uu____10795 with
          | (decls,env1) ->
              let uu____10806 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10806
              then
                let uu____10810 =
                  let uu____10812 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10812 in
                (uu____10810, env1)
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
             (fun uu____10840  ->
                fun lb  ->
                  match uu____10840 with
                  | (decls,env1) ->
                      let uu____10852 =
                        let uu____10856 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10856
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10852 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10870 = FStar_Syntax_Util.head_and_args t in
    match uu____10870 with
    | (hd1,args) ->
        let uu____10896 =
          let uu____10897 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10897.FStar_Syntax_Syntax.n in
        (match uu____10896 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10901,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10914 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10929  ->
      fun quals  ->
        match uu____10929 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10978 = FStar_Util.first_N nbinders formals in
              match uu____10978 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11018  ->
                         fun uu____11019  ->
                           match (uu____11018, uu____11019) with
                           | ((formal,uu____11029),(binder,uu____11031)) ->
                               let uu____11036 =
                                 let uu____11041 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11041) in
                               FStar_Syntax_Syntax.NT uu____11036) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11046 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11060  ->
                              match uu____11060 with
                              | (x,i) ->
                                  let uu____11067 =
                                    let uu___146_11068 = x in
                                    let uu____11069 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___146_11068.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___146_11068.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11069
                                    } in
                                  (uu____11067, i))) in
                    FStar_All.pipe_right uu____11046
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11081 =
                      let uu____11083 =
                        let uu____11084 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11084.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____11083 in
                    let uu____11088 =
                      let uu____11089 = FStar_Syntax_Subst.compress body in
                      let uu____11090 =
                        let uu____11091 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11091 in
                      FStar_Syntax_Syntax.extend_app_n uu____11089
                        uu____11090 in
                    uu____11088 uu____11081 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11133 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11133
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___147_11134 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___147_11134.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___147_11134.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___147_11134.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___147_11134.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___147_11134.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___147_11134.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___147_11134.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___147_11134.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___147_11134.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___147_11134.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___147_11134.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___147_11134.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___147_11134.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___147_11134.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___147_11134.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___147_11134.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___147_11134.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___147_11134.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___147_11134.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___147_11134.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___147_11134.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___147_11134.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___147_11134.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11155 = FStar_Syntax_Util.abs_formals e in
                match uu____11155 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11204::uu____11205 ->
                         let uu____11213 =
                           let uu____11214 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11214.FStar_Syntax_Syntax.n in
                         (match uu____11213 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11241 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11241 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11267 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11267
                                   then
                                     let uu____11285 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11285 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11331  ->
                                                   fun uu____11332  ->
                                                     match (uu____11331,
                                                             uu____11332)
                                                     with
                                                     | ((x,uu____11342),
                                                        (b,uu____11344)) ->
                                                         let uu____11349 =
                                                           let uu____11354 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11354) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11349)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11356 =
                                            let uu____11367 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11367) in
                                          (uu____11356, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11402 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11402 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11454) ->
                              let uu____11459 =
                                let uu____11470 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____11470 in
                              (uu____11459, true)
                          | uu____11503 when Prims.op_Negation norm1 ->
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
                          | uu____11505 ->
                              let uu____11506 =
                                let uu____11507 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11508 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11507
                                  uu____11508 in
                              failwith uu____11506)
                     | uu____11521 ->
                         let uu____11522 =
                           let uu____11523 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11523.FStar_Syntax_Syntax.n in
                         (match uu____11522 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11550 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11550 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11568 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11568 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11616 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11644 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11644
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11651 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11692  ->
                            fun lb  ->
                              match uu____11692 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11743 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11743
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11746 =
                                      let uu____11754 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11754
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11746 with
                                    | (tok,decl,env2) ->
                                        let uu____11779 =
                                          let uu____11786 =
                                            let uu____11792 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11792, tok) in
                                          uu____11786 :: toks in
                                        (uu____11779, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11651 with
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
                        | uu____11894 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11899 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11899 vars)
                            else
                              (let uu____11901 =
                                 let uu____11905 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11905) in
                               FStar_SMTEncoding_Util.mkApp uu____11901) in
                      let uu____11910 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_11912  ->
                                 match uu___116_11912 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11913 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11916 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11916))) in
                      if uu____11910
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11936;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11938;
                                FStar_Syntax_Syntax.lbeff = uu____11939;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11980 =
                                 let uu____11984 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11984 with
                                 | (tcenv',uu____11995,e_t) ->
                                     let uu____11999 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12006 -> failwith "Impossible" in
                                     (match uu____11999 with
                                      | (e1,t_norm1) ->
                                          ((let uu___150_12015 = env1 in
                                            {
                                              bindings =
                                                (uu___150_12015.bindings);
                                              depth = (uu___150_12015.depth);
                                              tcenv = tcenv';
                                              warn = (uu___150_12015.warn);
                                              cache = (uu___150_12015.cache);
                                              nolabels =
                                                (uu___150_12015.nolabels);
                                              use_zfuel_name =
                                                (uu___150_12015.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___150_12015.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___150_12015.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11980 with
                                | (env',e1,t_norm1) ->
                                    let uu____12022 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____12022 with
                                     | ((binders,body,uu____12034,uu____12035),curry)
                                         ->
                                         ((let uu____12042 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____12042
                                           then
                                             let uu____12043 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12044 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12043 uu____12044
                                           else ());
                                          (let uu____12046 =
                                             encode_binders None binders env' in
                                           match uu____12046 with
                                           | (vars,guards,env'1,binder_decls,uu____12062)
                                               ->
                                               let body1 =
                                                 let uu____12070 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12070
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12073 =
                                                 let uu____12078 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12078
                                                 then
                                                   let uu____12084 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12085 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12084, uu____12085)
                                                 else
                                                   (let uu____12091 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12091)) in
                                               (match uu____12073 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12105 =
                                                        let uu____12109 =
                                                          let uu____12110 =
                                                            let uu____12116 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12116) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12110 in
                                                        let uu____12122 =
                                                          let uu____12124 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12124 in
                                                        (uu____12109,
                                                          uu____12122,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12105 in
                                                    let uu____12126 =
                                                      let uu____12128 =
                                                        let uu____12130 =
                                                          let uu____12132 =
                                                            let uu____12134 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12134 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12132 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12130 in
                                                      FStar_List.append
                                                        decls1 uu____12128 in
                                                    (uu____12126, env1))))))
                           | uu____12137 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12156 = varops.fresh "fuel" in
                             (uu____12156, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12159 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12198  ->
                                     fun uu____12199  ->
                                       match (uu____12198, uu____12199) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12281 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12281 in
                                           let gtok =
                                             let uu____12283 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12283 in
                                           let env3 =
                                             let uu____12285 =
                                               let uu____12287 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12287 in
                                             push_free_var env2 flid gtok
                                               uu____12285 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12159 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12373
                                 t_norm uu____12375 =
                                 match (uu____12373, uu____12375) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12402;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12403;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12420 =
                                       let uu____12424 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12424 with
                                       | (tcenv',uu____12439,e_t) ->
                                           let uu____12443 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12450 ->
                                                 failwith "Impossible" in
                                           (match uu____12443 with
                                            | (e1,t_norm1) ->
                                                ((let uu___151_12459 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___151_12459.bindings);
                                                    depth =
                                                      (uu___151_12459.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___151_12459.warn);
                                                    cache =
                                                      (uu___151_12459.cache);
                                                    nolabels =
                                                      (uu___151_12459.nolabels);
                                                    use_zfuel_name =
                                                      (uu___151_12459.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___151_12459.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___151_12459.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12420 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12469 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12469
                                            then
                                              let uu____12470 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12471 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12472 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12470 uu____12471
                                                uu____12472
                                            else ());
                                           (let uu____12474 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12474 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12496 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12496
                                                  then
                                                    let uu____12497 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12498 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12499 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12500 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12497 uu____12498
                                                      uu____12499 uu____12500
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12504 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12504 with
                                                  | (vars,guards,env'1,binder_decls,uu____12522)
                                                      ->
                                                      let decl_g =
                                                        let uu____12530 =
                                                          let uu____12536 =
                                                            let uu____12538 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12538 in
                                                          (g, uu____12536,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12530 in
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
                                                        let uu____12553 =
                                                          let uu____12557 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12557) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12553 in
                                                      let gsapp =
                                                        let uu____12563 =
                                                          let uu____12567 =
                                                            let uu____12569 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12569 ::
                                                              vars_tm in
                                                          (g, uu____12567) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12563 in
                                                      let gmax =
                                                        let uu____12573 =
                                                          let uu____12577 =
                                                            let uu____12579 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12579 ::
                                                              vars_tm in
                                                          (g, uu____12577) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12573 in
                                                      let body1 =
                                                        let uu____12583 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12583
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12585 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12585 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12596
                                                               =
                                                               let uu____12600
                                                                 =
                                                                 let uu____12601
                                                                   =
                                                                   let uu____12609
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
                                                                    uu____12609) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12601 in
                                                               let uu____12620
                                                                 =
                                                                 let uu____12622
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12622 in
                                                               (uu____12600,
                                                                 uu____12620,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12596 in
                                                           let eqn_f =
                                                             let uu____12625
                                                               =
                                                               let uu____12629
                                                                 =
                                                                 let uu____12630
                                                                   =
                                                                   let uu____12636
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12636) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12630 in
                                                               (uu____12629,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12625 in
                                                           let eqn_g' =
                                                             let uu____12644
                                                               =
                                                               let uu____12648
                                                                 =
                                                                 let uu____12649
                                                                   =
                                                                   let uu____12655
                                                                    =
                                                                    let uu____12656
                                                                    =
                                                                    let uu____12659
                                                                    =
                                                                    let uu____12660
                                                                    =
                                                                    let uu____12664
                                                                    =
                                                                    let uu____12666
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12666
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12664) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12660 in
                                                                    (gsapp,
                                                                    uu____12659) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12656 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12655) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12649 in
                                                               (uu____12648,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12644 in
                                                           let uu____12678 =
                                                             let uu____12683
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12683
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12700)
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
                                                                    let uu____12715
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12715
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12718
                                                                    =
                                                                    let uu____12722
                                                                    =
                                                                    let uu____12723
                                                                    =
                                                                    let uu____12729
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12729) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12723 in
                                                                    (uu____12722,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12718 in
                                                                 let uu____12740
                                                                   =
                                                                   let uu____12744
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12744
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12752
                                                                    =
                                                                    let uu____12754
                                                                    =
                                                                    let uu____12755
                                                                    =
                                                                    let uu____12759
                                                                    =
                                                                    let uu____12760
                                                                    =
                                                                    let uu____12766
                                                                    =
                                                                    let uu____12767
                                                                    =
                                                                    let uu____12770
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12770,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12767 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12766) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12760 in
                                                                    (uu____12759,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12755 in
                                                                    [uu____12754] in
                                                                    (d3,
                                                                    uu____12752) in
                                                                 (match uu____12740
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12678
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
                               let uu____12805 =
                                 let uu____12812 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12848  ->
                                      fun uu____12849  ->
                                        match (uu____12848, uu____12849) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12935 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12935 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12812 in
                               (match uu____12805 with
                                | (decls2,eqns,env01) ->
                                    let uu____12975 =
                                      let isDeclFun uu___117_12983 =
                                        match uu___117_12983 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12984 -> true
                                        | uu____12990 -> false in
                                      let uu____12991 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12991
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12975 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____13018 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____13018
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
        let uu____13051 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13051 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____13054 = encode_sigelt' env se in
      match uu____13054 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13064 =
                  let uu____13065 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13065 in
                [uu____13064]
            | uu____13066 ->
                let uu____13067 =
                  let uu____13069 =
                    let uu____13070 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13070 in
                  uu____13069 :: g in
                let uu____13071 =
                  let uu____13073 =
                    let uu____13074 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13074 in
                  [uu____13073] in
                FStar_List.append uu____13067 uu____13071 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13082 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13085 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13087 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13089 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13097 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13100 =
            let uu____13101 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13101 Prims.op_Negation in
          if uu____13100
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13121 ->
                   let uu____13122 =
                     let uu____13125 =
                       let uu____13126 =
                         let uu____13141 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13141) in
                       FStar_Syntax_Syntax.Tm_abs uu____13126 in
                     FStar_Syntax_Syntax.mk uu____13125 in
                   uu____13122 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13194 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13194 with
               | (aname,atok,env2) ->
                   let uu____13204 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13204 with
                    | (formals,uu____13214) ->
                        let uu____13221 =
                          let uu____13224 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13224 env2 in
                        (match uu____13221 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13232 =
                                 let uu____13233 =
                                   let uu____13239 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13247  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13239,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13233 in
                               [uu____13232;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13254 =
                               let aux uu____13283 uu____13284 =
                                 match (uu____13283, uu____13284) with
                                 | ((bv,uu____13311),(env3,acc_sorts,acc)) ->
                                     let uu____13332 = gen_term_var env3 bv in
                                     (match uu____13332 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13254 with
                              | (uu____13370,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13384 =
                                      let uu____13388 =
                                        let uu____13389 =
                                          let uu____13395 =
                                            let uu____13396 =
                                              let uu____13399 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13399) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13396 in
                                          ([[app]], xs_sorts, uu____13395) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13389 in
                                      (uu____13388, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13384 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13411 =
                                      let uu____13415 =
                                        let uu____13416 =
                                          let uu____13422 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13422) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13416 in
                                      (uu____13415,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13411 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13432 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13432 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13448,uu____13449)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13450 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13450 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13461,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13466 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13468  ->
                      match uu___118_13468 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13469 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13472 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13473 -> false)) in
            Prims.op_Negation uu____13466 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13479 = encode_top_level_val env fv t quals in
             match uu____13479 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13491 =
                   let uu____13493 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13493 in
                 (uu____13491, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13498 = encode_formula f env in
          (match uu____13498 with
           | (f1,decls) ->
               let g =
                 let uu____13507 =
                   let uu____13508 =
                     let uu____13512 =
                       let uu____13514 =
                         let uu____13515 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13515 in
                       Some uu____13514 in
                     let uu____13516 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13512, uu____13516) in
                   FStar_SMTEncoding_Util.mkAssume uu____13508 in
                 [uu____13507] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13520,uu____13521) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13527 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13534 =
                       let uu____13539 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13539.FStar_Syntax_Syntax.fv_name in
                     uu____13534.FStar_Syntax_Syntax.v in
                   let uu____13543 =
                     let uu____13544 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13544 in
                   if uu____13543
                   then
                     let val_decl =
                       let uu___152_13559 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___152_13559.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___152_13559.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___152_13559.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13563 = encode_sigelt' env1 val_decl in
                     match uu____13563 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____13527 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13580,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13582;
                          FStar_Syntax_Syntax.lbtyp = uu____13583;
                          FStar_Syntax_Syntax.lbeff = uu____13584;
                          FStar_Syntax_Syntax.lbdef = uu____13585;_}::[]),uu____13586,uu____13587)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13601 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13601 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13624 =
                   let uu____13626 =
                     let uu____13627 =
                       let uu____13631 =
                         let uu____13632 =
                           let uu____13638 =
                             let uu____13639 =
                               let uu____13642 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13642) in
                             FStar_SMTEncoding_Util.mkEq uu____13639 in
                           ([[b2t_x]], [xx], uu____13638) in
                         FStar_SMTEncoding_Util.mkForall uu____13632 in
                       (uu____13631, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13627 in
                   [uu____13626] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13624 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13659,uu____13660,uu____13661)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_13667  ->
                  match uu___119_13667 with
                  | FStar_Syntax_Syntax.Discriminator uu____13668 -> true
                  | uu____13669 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13671,lids,uu____13673) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13680 =
                     let uu____13681 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13681.FStar_Ident.idText in
                   uu____13680 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_13683  ->
                     match uu___120_13683 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13684 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13687,uu____13688)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_13698  ->
                  match uu___121_13698 with
                  | FStar_Syntax_Syntax.Projector uu____13699 -> true
                  | uu____13702 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13709 = try_lookup_free_var env l in
          (match uu____13709 with
           | Some uu____13713 -> ([], env)
           | None  ->
               let se1 =
                 let uu___153_13716 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___153_13716.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___153_13716.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13722,uu____13723) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13735) ->
          let uu____13740 = encode_sigelts env ses in
          (match uu____13740 with
           | (g,env1) ->
               let uu____13750 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_13760  ->
                         match uu___122_13760 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13761;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13762;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13763;_}
                             -> false
                         | uu____13765 -> true)) in
               (match uu____13750 with
                | (g',inversions) ->
                    let uu____13774 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_13784  ->
                              match uu___123_13784 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13785 ->
                                  true
                              | uu____13791 -> false)) in
                    (match uu____13774 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13802,tps,k,uu____13805,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_13815  ->
                    match uu___124_13815 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13816 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13823 = c in
              match uu____13823 with
              | (name,args,uu____13827,uu____13828,uu____13829) ->
                  let uu____13832 =
                    let uu____13833 =
                      let uu____13839 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13846  ->
                                match uu____13846 with
                                | (uu____13850,sort,uu____13852) -> sort)) in
                      (name, uu____13839, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13833 in
                  [uu____13832]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13870 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13873 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13873 FStar_Option.isNone)) in
            if uu____13870
            then []
            else
              (let uu____13890 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13890 with
               | (xxsym,xx) ->
                   let uu____13896 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13907  ->
                             fun l  ->
                               match uu____13907 with
                               | (out,decls) ->
                                   let uu____13919 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13919 with
                                    | (uu____13925,data_t) ->
                                        let uu____13927 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13927 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13956 =
                                                 let uu____13957 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13957.FStar_Syntax_Syntax.n in
                                               match uu____13956 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13965,indices) ->
                                                   indices
                                               | uu____13981 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13993  ->
                                                         match uu____13993
                                                         with
                                                         | (x,uu____13997) ->
                                                             let uu____13998
                                                               =
                                                               let uu____13999
                                                                 =
                                                                 let uu____14003
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____14003,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13999 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13998)
                                                    env) in
                                             let uu____14005 =
                                               encode_args indices env1 in
                                             (match uu____14005 with
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
                                                      let uu____14025 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14033
                                                                 =
                                                                 let uu____14036
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____14036,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14033)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____14025
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____14038 =
                                                      let uu____14039 =
                                                        let uu____14042 =
                                                          let uu____14043 =
                                                            let uu____14046 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____14046,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14043 in
                                                        (out, uu____14042) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14039 in
                                                    (uu____14038,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13896 with
                    | (data_ax,decls) ->
                        let uu____14054 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14054 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14065 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14065 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14068 =
                                 let uu____14072 =
                                   let uu____14073 =
                                     let uu____14079 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14087 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14079,
                                       uu____14087) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14073 in
                                 let uu____14095 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14072, (Some "inversion axiom"),
                                   uu____14095) in
                               FStar_SMTEncoding_Util.mkAssume uu____14068 in
                             let pattern_guarded_inversion =
                               let uu____14099 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14099
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14107 =
                                   let uu____14108 =
                                     let uu____14112 =
                                       let uu____14113 =
                                         let uu____14119 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14127 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14119, uu____14127) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14113 in
                                     let uu____14135 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14112, (Some "inversion axiom"),
                                       uu____14135) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14108 in
                                 [uu____14107]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14138 =
            let uu____14146 =
              let uu____14147 = FStar_Syntax_Subst.compress k in
              uu____14147.FStar_Syntax_Syntax.n in
            match uu____14146 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14176 -> (tps, k) in
          (match uu____14138 with
           | (formals,res) ->
               let uu____14191 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14191 with
                | (formals1,res1) ->
                    let uu____14198 = encode_binders None formals1 env in
                    (match uu____14198 with
                     | (vars,guards,env',binder_decls,uu____14213) ->
                         let uu____14220 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14220 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14233 =
                                  let uu____14237 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14237) in
                                FStar_SMTEncoding_Util.mkApp uu____14233 in
                              let uu____14242 =
                                let tname_decl =
                                  let uu____14248 =
                                    let uu____14249 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14264  ->
                                              match uu____14264 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14272 = varops.next_id () in
                                    (tname, uu____14249,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14272, false) in
                                  constructor_or_logic_type_decl uu____14248 in
                                let uu____14277 =
                                  match vars with
                                  | [] ->
                                      let uu____14284 =
                                        let uu____14285 =
                                          let uu____14287 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14287 in
                                        push_free_var env1 t tname
                                          uu____14285 in
                                      ([], uu____14284)
                                  | uu____14291 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14297 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14297 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14306 =
                                          let uu____14310 =
                                            let uu____14311 =
                                              let uu____14319 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14319) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14311 in
                                          (uu____14310,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14306 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14277 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14242 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14342 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14342 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14356 =
                                               let uu____14357 =
                                                 let uu____14361 =
                                                   let uu____14362 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14362 in
                                                 (uu____14361,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14357 in
                                             [uu____14356]
                                           else [] in
                                         let uu____14365 =
                                           let uu____14367 =
                                             let uu____14369 =
                                               let uu____14370 =
                                                 let uu____14374 =
                                                   let uu____14375 =
                                                     let uu____14381 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14381) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14375 in
                                                 (uu____14374, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14370 in
                                             [uu____14369] in
                                           FStar_List.append karr uu____14367 in
                                         FStar_List.append decls1 uu____14365 in
                                   let aux =
                                     let uu____14390 =
                                       let uu____14392 =
                                         inversion_axioms tapp vars in
                                       let uu____14394 =
                                         let uu____14396 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14396] in
                                       FStar_List.append uu____14392
                                         uu____14394 in
                                     FStar_List.append kindingAx uu____14390 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14401,uu____14402,uu____14403,uu____14404,uu____14405)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14410,t,uu____14412,n_tps,uu____14414) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14419 = new_term_constant_and_tok_from_lid env d in
          (match uu____14419 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14430 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14430 with
                | (formals,t_res) ->
                    let uu____14452 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14452 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14461 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14461 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14499 =
                                            mk_term_projector_name d x in
                                          (uu____14499,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14501 =
                                  let uu____14511 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14511, true) in
                                FStar_All.pipe_right uu____14501
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
                              let uu____14533 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14533 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14541::uu____14542 ->
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
                                         let uu____14567 =
                                           let uu____14573 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14573) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14567
                                     | uu____14586 -> tok_typing in
                                   let uu____14591 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14591 with
                                    | (vars',guards',env'',decls_formals,uu____14606)
                                        ->
                                        let uu____14613 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14613 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14632 ->
                                                   let uu____14636 =
                                                     let uu____14637 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14637 in
                                                   [uu____14636] in
                                             let encode_elim uu____14644 =
                                               let uu____14645 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14645 with
                                               | (head1,args) ->
                                                   let uu____14674 =
                                                     let uu____14675 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14675.FStar_Syntax_Syntax.n in
                                                   (match uu____14674 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____14682;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14683;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14684;_},uu____14685)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14695 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14695
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
                                                                 | uu____14721
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14729
                                                                    =
                                                                    let uu____14730
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14730 in
                                                                    if
                                                                    uu____14729
                                                                    then
                                                                    let uu____14737
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14737]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14739
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14752
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14752
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14774
                                                                    =
                                                                    let uu____14778
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14778 in
                                                                    (match uu____14774
                                                                    with
                                                                    | 
                                                                    (uu____14785,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14791
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14791
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14793
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14793
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
                                                             (match uu____14739
                                                              with
                                                              | (uu____14801,arg_vars,elim_eqns_or_guards,uu____14804)
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
                                                                    let uu____14823
                                                                    =
                                                                    let uu____14827
                                                                    =
                                                                    let uu____14828
                                                                    =
                                                                    let uu____14834
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14840
                                                                    =
                                                                    let uu____14841
                                                                    =
                                                                    let uu____14844
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14844) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14841 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14834,
                                                                    uu____14840) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14828 in
                                                                    (uu____14827,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14823 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14857
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14857,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14859
                                                                    =
                                                                    let uu____14863
                                                                    =
                                                                    let uu____14864
                                                                    =
                                                                    let uu____14870
                                                                    =
                                                                    let uu____14873
                                                                    =
                                                                    let uu____14875
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14875] in
                                                                    [uu____14873] in
                                                                    let uu____14878
                                                                    =
                                                                    let uu____14879
                                                                    =
                                                                    let uu____14882
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14883
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14882,
                                                                    uu____14883) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14879 in
                                                                    (uu____14870,
                                                                    [x],
                                                                    uu____14878) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14864 in
                                                                    let uu____14893
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14863,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14893) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14859
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14898
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
                                                                    (let uu____14913
                                                                    =
                                                                    let uu____14914
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14914
                                                                    dapp1 in
                                                                    [uu____14913]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14898
                                                                    FStar_List.flatten in
                                                                    let uu____14918
                                                                    =
                                                                    let uu____14922
                                                                    =
                                                                    let uu____14923
                                                                    =
                                                                    let uu____14929
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14935
                                                                    =
                                                                    let uu____14936
                                                                    =
                                                                    let uu____14939
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14939) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14936 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14929,
                                                                    uu____14935) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14923 in
                                                                    (uu____14922,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14918) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14955 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14955
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
                                                                 | uu____14981
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14989
                                                                    =
                                                                    let uu____14990
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14990 in
                                                                    if
                                                                    uu____14989
                                                                    then
                                                                    let uu____14997
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14997]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14999
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15012
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15012
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15034
                                                                    =
                                                                    let uu____15038
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15038 in
                                                                    (match uu____15034
                                                                    with
                                                                    | 
                                                                    (uu____15045,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15051
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15051
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15053
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15053
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
                                                             (match uu____14999
                                                              with
                                                              | (uu____15061,arg_vars,elim_eqns_or_guards,uu____15064)
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
                                                                    let uu____15083
                                                                    =
                                                                    let uu____15087
                                                                    =
                                                                    let uu____15088
                                                                    =
                                                                    let uu____15094
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15100
                                                                    =
                                                                    let uu____15101
                                                                    =
                                                                    let uu____15104
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15104) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15101 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15094,
                                                                    uu____15100) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15088 in
                                                                    (uu____15087,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15083 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15117
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15117,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15119
                                                                    =
                                                                    let uu____15123
                                                                    =
                                                                    let uu____15124
                                                                    =
                                                                    let uu____15130
                                                                    =
                                                                    let uu____15133
                                                                    =
                                                                    let uu____15135
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15135] in
                                                                    [uu____15133] in
                                                                    let uu____15138
                                                                    =
                                                                    let uu____15139
                                                                    =
                                                                    let uu____15142
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15143
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15142,
                                                                    uu____15143) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15139 in
                                                                    (uu____15130,
                                                                    [x],
                                                                    uu____15138) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15124 in
                                                                    let uu____15153
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15123,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15153) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15119
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15158
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
                                                                    (let uu____15173
                                                                    =
                                                                    let uu____15174
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15174
                                                                    dapp1 in
                                                                    [uu____15173]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15158
                                                                    FStar_List.flatten in
                                                                    let uu____15178
                                                                    =
                                                                    let uu____15182
                                                                    =
                                                                    let uu____15183
                                                                    =
                                                                    let uu____15189
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15195
                                                                    =
                                                                    let uu____15196
                                                                    =
                                                                    let uu____15199
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15199) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15196 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15189,
                                                                    uu____15195) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15183 in
                                                                    (uu____15182,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15178) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15209 ->
                                                        ((let uu____15211 =
                                                            let uu____15212 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15213 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15212
                                                              uu____15213 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15211);
                                                         ([], []))) in
                                             let uu____15216 = encode_elim () in
                                             (match uu____15216 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15228 =
                                                      let uu____15230 =
                                                        let uu____15232 =
                                                          let uu____15234 =
                                                            let uu____15236 =
                                                              let uu____15237
                                                                =
                                                                let uu____15243
                                                                  =
                                                                  let uu____15245
                                                                    =
                                                                    let uu____15246
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15246 in
                                                                  Some
                                                                    uu____15245 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15243) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15237 in
                                                            [uu____15236] in
                                                          let uu____15249 =
                                                            let uu____15251 =
                                                              let uu____15253
                                                                =
                                                                let uu____15255
                                                                  =
                                                                  let uu____15257
                                                                    =
                                                                    let uu____15259
                                                                    =
                                                                    let uu____15261
                                                                    =
                                                                    let uu____15262
                                                                    =
                                                                    let uu____15266
                                                                    =
                                                                    let uu____15267
                                                                    =
                                                                    let uu____15273
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15273) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15267 in
                                                                    (uu____15266,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15262 in
                                                                    let uu____15280
                                                                    =
                                                                    let uu____15282
                                                                    =
                                                                    let uu____15283
                                                                    =
                                                                    let uu____15287
                                                                    =
                                                                    let uu____15288
                                                                    =
                                                                    let uu____15294
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____15300
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15294,
                                                                    uu____15300) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15288 in
                                                                    (uu____15287,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15283 in
                                                                    [uu____15282] in
                                                                    uu____15261
                                                                    ::
                                                                    uu____15280 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15259 in
                                                                  FStar_List.append
                                                                    uu____15257
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15255 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15253 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15251 in
                                                          FStar_List.append
                                                            uu____15234
                                                            uu____15249 in
                                                        FStar_List.append
                                                          decls3 uu____15232 in
                                                      FStar_List.append
                                                        decls2 uu____15230 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15228 in
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
           (fun uu____15321  ->
              fun se  ->
                match uu____15321 with
                | (g,env1) ->
                    let uu____15333 = encode_sigelt env1 se in
                    (match uu____15333 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15369 =
        match uu____15369 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15387 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____15392 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15392
                   then
                     let uu____15393 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15394 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15395 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15393 uu____15394 uu____15395
                   else ());
                  (let uu____15397 = encode_term t1 env1 in
                   match uu____15397 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15407 =
                         let uu____15411 =
                           let uu____15412 =
                             let uu____15413 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15413
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15412 in
                         new_term_constant_from_string env1 x uu____15411 in
                       (match uu____15407 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15424 = FStar_Options.log_queries () in
                              if uu____15424
                              then
                                let uu____15426 =
                                  let uu____15427 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15428 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15429 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15427 uu____15428 uu____15429 in
                                Some uu____15426
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15440,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15449 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15449 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15462,se,uu____15464) ->
                 let uu____15467 = encode_sigelt env1 se in
                 (match uu____15467 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15477,se) ->
                 let uu____15481 = encode_sigelt env1 se in
                 (match uu____15481 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15491 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15491 with | (uu____15503,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15548  ->
            match uu____15548 with
            | (l,uu____15555,uu____15556) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15577  ->
            match uu____15577 with
            | (l,uu____15585,uu____15586) ->
                let uu____15591 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39) (
                    fst l) in
                let uu____15592 =
                  let uu____15594 =
                    let uu____15595 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15595 in
                  [uu____15594] in
                uu____15591 :: uu____15592)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15606 =
      let uu____15608 =
        let uu____15609 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15611 =
          let uu____15612 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15612 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15609;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15611
        } in
      [uu____15608] in
    FStar_ST.write last_env uu____15606
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15622 = FStar_ST.read last_env in
      match uu____15622 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15628 ->
          let uu___154_15630 = e in
          let uu____15631 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___154_15630.bindings);
            depth = (uu___154_15630.depth);
            tcenv;
            warn = (uu___154_15630.warn);
            cache = (uu___154_15630.cache);
            nolabels = (uu___154_15630.nolabels);
            use_zfuel_name = (uu___154_15630.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15630.encode_non_total_function_typ);
            current_module_name = uu____15631
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15635 = FStar_ST.read last_env in
    match uu____15635 with
    | [] -> failwith "Empty env stack"
    | uu____15640::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15648  ->
    let uu____15649 = FStar_ST.read last_env in
    match uu____15649 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___155_15660 = hd1 in
          {
            bindings = (uu___155_15660.bindings);
            depth = (uu___155_15660.depth);
            tcenv = (uu___155_15660.tcenv);
            warn = (uu___155_15660.warn);
            cache = refs;
            nolabels = (uu___155_15660.nolabels);
            use_zfuel_name = (uu___155_15660.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_15660.encode_non_total_function_typ);
            current_module_name = (uu___155_15660.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15666  ->
    let uu____15667 = FStar_ST.read last_env in
    match uu____15667 with
    | [] -> failwith "Popping an empty stack"
    | uu____15672::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15680  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15683  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15686  ->
    let uu____15687 = FStar_ST.read last_env in
    match uu____15687 with
    | hd1::uu____15693::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15699 -> failwith "Impossible"
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
        | (uu____15748::uu____15749,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___156_15753 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___156_15753.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___156_15753.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___156_15753.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15754 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15765 =
        let uu____15767 =
          let uu____15768 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15768 in
        let uu____15769 = open_fact_db_tags env in uu____15767 :: uu____15769 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15765
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
      let uu____15784 = encode_sigelt env se in
      match uu____15784 with
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
        let uu____15809 = FStar_Options.log_queries () in
        if uu____15809
        then
          let uu____15811 =
            let uu____15812 =
              let uu____15813 =
                let uu____15814 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15814 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15813 in
            FStar_SMTEncoding_Term.Caption uu____15812 in
          uu____15811 :: decls
        else decls in
      let env =
        let uu____15821 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15821 tcenv in
      let uu____15822 = encode_top_level_facts env se in
      match uu____15822 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15831 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15831))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15842 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15842
       then
         let uu____15843 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15843
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15864  ->
                 fun se  ->
                   match uu____15864 with
                   | (g,env2) ->
                       let uu____15876 = encode_top_level_facts env2 se in
                       (match uu____15876 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15889 =
         encode_signature
           (let uu___157_15893 = env in
            {
              bindings = (uu___157_15893.bindings);
              depth = (uu___157_15893.depth);
              tcenv = (uu___157_15893.tcenv);
              warn = false;
              cache = (uu___157_15893.cache);
              nolabels = (uu___157_15893.nolabels);
              use_zfuel_name = (uu___157_15893.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___157_15893.encode_non_total_function_typ);
              current_module_name = (uu___157_15893.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15889 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15905 = FStar_Options.log_queries () in
             if uu____15905
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___158_15910 = env1 in
               {
                 bindings = (uu___158_15910.bindings);
                 depth = (uu___158_15910.depth);
                 tcenv = (uu___158_15910.tcenv);
                 warn = true;
                 cache = (uu___158_15910.cache);
                 nolabels = (uu___158_15910.nolabels);
                 use_zfuel_name = (uu___158_15910.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___158_15910.encode_non_total_function_typ);
                 current_module_name = (uu___158_15910.current_module_name)
               });
            (let uu____15912 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15912
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
        (let uu____15947 =
           let uu____15948 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15948.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15947);
        (let env =
           let uu____15950 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15950 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15957 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15978 = aux rest in
                 (match uu____15978 with
                  | (out,rest1) ->
                      let t =
                        let uu____15996 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15996 with
                        | Some uu____16000 ->
                            let uu____16001 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16001
                              x.FStar_Syntax_Syntax.sort
                        | uu____16002 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____16005 =
                        let uu____16007 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___159_16008 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___159_16008.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___159_16008.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16007 :: out in
                      (uu____16005, rest1))
             | uu____16011 -> ([], bindings1) in
           let uu____16015 = aux bindings in
           match uu____16015 with
           | (closing,bindings1) ->
               let uu____16029 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16029, bindings1) in
         match uu____15957 with
         | (q1,bindings1) ->
             let uu____16042 =
               let uu____16045 =
                 FStar_List.filter
                   (fun uu___125_16047  ->
                      match uu___125_16047 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16048 ->
                          false
                      | uu____16052 -> true) bindings1 in
               encode_env_bindings env uu____16045 in
             (match uu____16042 with
              | (env_decls,env1) ->
                  ((let uu____16063 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16063
                    then
                      let uu____16064 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16064
                    else ());
                   (let uu____16066 = encode_formula q1 env1 in
                    match uu____16066 with
                    | (phi,qdecls) ->
                        let uu____16078 =
                          let uu____16081 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16081 phi in
                        (match uu____16078 with
                         | (labels,phi1) ->
                             let uu____16091 = encode_labels labels in
                             (match uu____16091 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____16112 =
                                      let uu____16116 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16117 =
                                        varops.mk_unique "@query" in
                                      (uu____16116, (Some "query"),
                                        uu____16117) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16112 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16130 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16130 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16132 = encode_formula q env in
       match uu____16132 with
       | (f,uu____16136) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16138) -> true
             | uu____16141 -> false)))