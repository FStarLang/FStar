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
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option) option
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
               (fun uu___109_1777  ->
                  match uu___109_1777 with
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
  fun uu___110_1882  ->
    match uu___110_1882 with
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
  fun uu___111_2039  ->
    match uu___111_2039 with
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
                           (let uu___136_2968 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___136_2968.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___136_2968.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___136_2968.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___136_2968.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___136_2968.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___136_2968.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___136_2968.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___136_2968.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___136_2968.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___136_2968.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___136_2968.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___136_2968.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___136_2968.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___136_2968.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___136_2968.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___136_2968.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___136_2968.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___136_2968.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___136_2968.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___136_2968.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___136_2968.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___136_2968.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___136_2968.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___136_2968.FStar_TypeChecker_Env.proof_ns)
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
                                         let x_has_base_t =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             xtm base_t in
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
                                           let uu____3395 =
                                             let uu____3399 =
                                               let uu____3400 =
                                                 let uu____3406 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3406) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3400 in
                                             (uu____3399,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3395 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____3421 =
                                             let uu____3425 =
                                               let uu____3426 =
                                                 let uu____3432 =
                                                   let uu____3433 =
                                                     let uu____3436 =
                                                       let uu____3437 =
                                                         let uu____3443 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____3443) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____3437 in
                                                     (uu____3436, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____3433 in
                                                 ([[valid_t]], cvars1,
                                                   uu____3432) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3426 in
                                             (uu____3425,
                                               (Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3421 in
                                         let t_kinding =
                                           let uu____3463 =
                                             let uu____3467 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3467,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3463 in
                                         let t_interp =
                                           let uu____3477 =
                                             let uu____3481 =
                                               let uu____3482 =
                                                 let uu____3488 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3488) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3482 in
                                             let uu____3500 =
                                               let uu____3502 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3502 in
                                             (uu____3481, uu____3500,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3477 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3507 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3507);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3524 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3524 in
           let uu____3525 = encode_term_pred None k env ttm in
           (match uu____3525 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3533 =
                    let uu____3537 =
                      let uu____3538 =
                        let uu____3539 =
                          let uu____3540 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3540 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3539 in
                      varops.mk_unique uu____3538 in
                    (t_has_k, (Some "Uvar typing"), uu____3537) in
                  FStar_SMTEncoding_Util.mkAssume uu____3533 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3543 ->
           let uu____3553 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3553 with
            | (head1,args_e) ->
                let uu____3581 =
                  let uu____3589 =
                    let uu____3590 = FStar_Syntax_Subst.compress head1 in
                    uu____3590.FStar_Syntax_Syntax.n in
                  (uu____3589, args_e) in
                (match uu____3581 with
                 | uu____3600 when head_redex env head1 ->
                     let uu____3608 = whnf env t in
                     encode_term uu____3608 env
                 | uu____3609 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____3622;
                       FStar_Syntax_Syntax.pos = uu____3623;
                       FStar_Syntax_Syntax.vars = uu____3624;_},uu____3625),uu____3626::
                    (v1,uu____3628)::(v2,uu____3630)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3668 = encode_term v1 env in
                     (match uu____3668 with
                      | (v11,decls1) ->
                          let uu____3675 = encode_term v2 env in
                          (match uu____3675 with
                           | (v21,decls2) ->
                               let uu____3682 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3682,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3685::(v1,uu____3687)::(v2,uu____3689)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3723 = encode_term v1 env in
                     (match uu____3723 with
                      | (v11,decls1) ->
                          let uu____3730 = encode_term v2 env in
                          (match uu____3730 with
                           | (v21,decls2) ->
                               let uu____3737 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3737,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3739) ->
                     let e0 =
                       let uu____3751 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3751 in
                     ((let uu____3757 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3757
                       then
                         let uu____3758 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3758
                       else ());
                      (let e =
                         let uu____3763 =
                           let uu____3764 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3765 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3764
                             uu____3765 in
                         uu____3763 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3774),(arg,uu____3776)::[]) -> encode_term arg env
                 | uu____3794 ->
                     let uu____3802 = encode_args args_e env in
                     (match uu____3802 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3835 = encode_term head1 env in
                            match uu____3835 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3874 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3874 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3916  ->
                                                 fun uu____3917  ->
                                                   match (uu____3916,
                                                           uu____3917)
                                                   with
                                                   | ((bv,uu____3931),
                                                      (a,uu____3933)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3947 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3947
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3952 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3952 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3962 =
                                                   let uu____3966 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3971 =
                                                     let uu____3972 =
                                                       let uu____3973 =
                                                         let uu____3974 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3974 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3973 in
                                                     varops.mk_unique
                                                       uu____3972 in
                                                   (uu____3966,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3971) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3962 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3991 = lookup_free_var_sym env fv in
                            match uu____3991 with
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
                                   FStar_Syntax_Syntax.tk = uu____4014;
                                   FStar_Syntax_Syntax.pos = uu____4015;
                                   FStar_Syntax_Syntax.vars = uu____4016;_},uu____4017)
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____4028;
                                   FStar_Syntax_Syntax.pos = uu____4029;
                                   FStar_Syntax_Syntax.vars = uu____4030;_},uu____4031)
                                ->
                                let uu____4036 =
                                  let uu____4037 =
                                    let uu____4040 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4040
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4037
                                    FStar_Pervasives.snd in
                                Some uu____4036
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4060 =
                                  let uu____4061 =
                                    let uu____4064 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4064
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4061
                                    FStar_Pervasives.snd in
                                Some uu____4060
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4083,(FStar_Util.Inl t1,uu____4085),uu____4086)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4124,(FStar_Util.Inr c,uu____4126),uu____4127)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4165 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4185 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4185 in
                               let uu____4186 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4186 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4196;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4197;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4198;_},uu____4199)
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
                                     | uu____4223 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4268 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4268 with
            | (bs1,body1,opening) ->
                let fallback uu____4283 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____4288 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4288, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4299 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____4299
                  | FStar_Util.Inr (eff,uu____4301) ->
                      let uu____4307 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____4307 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4352 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___137_4353 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___137_4353.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___137_4353.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___137_4353.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___137_4353.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___137_4353.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___137_4353.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___137_4353.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___137_4353.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___137_4353.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___137_4353.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___137_4353.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___137_4353.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___137_4353.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___137_4353.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___137_4353.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___137_4353.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___137_4353.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___137_4353.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___137_4353.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___137_4353.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___137_4353.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___137_4353.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___137_4353.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___137_4353.FStar_TypeChecker_Env.proof_ns)
                             }) uu____4352 FStar_Syntax_Syntax.U_unknown in
                        let uu____4354 =
                          let uu____4355 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4355 in
                        FStar_Util.Inl uu____4354
                    | FStar_Util.Inr (eff_name,uu____4362) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4393 =
                        let uu____4394 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4394 in
                      FStar_All.pipe_right uu____4393
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4406 =
                        let uu____4407 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4407 FStar_Pervasives.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4415 =
                          let uu____4416 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4416 in
                        FStar_All.pipe_right uu____4415
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4420 =
                             let uu____4421 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4421 in
                           FStar_All.pipe_right uu____4420
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4432 =
                         let uu____4433 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4433 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4432);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4448 =
                       (is_impure lc1) &&
                         (let uu____4449 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4449) in
                     if uu____4448
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4454 = encode_binders None bs1 env in
                        match uu____4454 with
                        | (vars,guards,envbody,decls,uu____4469) ->
                            let uu____4476 =
                              let uu____4484 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4484
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4476 with
                             | (lc2,body2) ->
                                 let uu____4509 = encode_term body2 envbody in
                                 (match uu____4509 with
                                  | (body3,decls') ->
                                      let uu____4516 =
                                        let uu____4521 = codomain_eff lc2 in
                                        match uu____4521 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4533 =
                                              encode_term tfun env in
                                            (match uu____4533 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4516 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4552 =
                                               let uu____4558 =
                                                 let uu____4559 =
                                                   let uu____4562 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4562, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4559 in
                                               ([], vars, uu____4558) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4552 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4570 =
                                                   let uu____4572 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4572 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4570 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4583 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4583 with
                                            | Some cache_entry ->
                                                let uu____4588 =
                                                  let uu____4589 =
                                                    let uu____4593 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4593) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4589 in
                                                (uu____4588,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | None  ->
                                                let uu____4599 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4599 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4606 =
                                                         let uu____4607 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4607 =
                                                           cache_size in
                                                       if uu____4606
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
                                                         let uu____4618 =
                                                           let uu____4619 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4619 in
                                                         varops.mk_unique
                                                           uu____4618 in
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
                                                       let uu____4624 =
                                                         let uu____4628 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4628) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4624 in
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
                                                           let uu____4640 =
                                                             let uu____4641 =
                                                               let uu____4645
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4645,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4641 in
                                                           [uu____4640] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4653 =
                                                         let uu____4657 =
                                                           let uu____4658 =
                                                             let uu____4664 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4664) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4658 in
                                                         (uu____4657,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4653 in
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
                                                     ((let uu____4674 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4674);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4676,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4677;
                          FStar_Syntax_Syntax.lbunivs = uu____4678;
                          FStar_Syntax_Syntax.lbtyp = uu____4679;
                          FStar_Syntax_Syntax.lbeff = uu____4680;
                          FStar_Syntax_Syntax.lbdef = uu____4681;_}::uu____4682),uu____4683)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4701;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4703;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4719 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4732 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4732, [decl_e])))
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
              let uu____4774 = encode_term e1 env in
              match uu____4774 with
              | (ee1,decls1) ->
                  let uu____4781 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4781 with
                   | (xs,e21) ->
                       let uu____4795 = FStar_List.hd xs in
                       (match uu____4795 with
                        | (x1,uu____4803) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4805 = encode_body e21 env' in
                            (match uu____4805 with
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
            let uu____4827 =
              let uu____4831 =
                let uu____4832 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4832 in
              gen_term_var env uu____4831 in
            match uu____4827 with
            | (scrsym,scr',env1) ->
                let uu____4842 = encode_term e env1 in
                (match uu____4842 with
                 | (scr,decls) ->
                     let uu____4849 =
                       let encode_branch b uu____4865 =
                         match uu____4865 with
                         | (else_case,decls1) ->
                             let uu____4876 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4876 with
                              | (p,w,br) ->
                                  let uu____4897 = encode_pat env1 p in
                                  (match uu____4897 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____4917  ->
                                                   match uu____4917 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____4922 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____4937 =
                                               encode_term w1 env2 in
                                             (match uu____4937 with
                                              | (w2,decls2) ->
                                                  let uu____4945 =
                                                    let uu____4946 =
                                                      let uu____4949 =
                                                        let uu____4950 =
                                                          let uu____4953 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____4953) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____4950 in
                                                      (guard, uu____4949) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____4946 in
                                                  (uu____4945, decls2)) in
                                       (match uu____4922 with
                                        | (guard1,decls2) ->
                                            let uu____4961 =
                                              encode_br br env2 in
                                            (match uu____4961 with
                                             | (br1,decls3) ->
                                                 let uu____4969 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____4969,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4849 with
                      | (match_tm,decls1) ->
                          let uu____4980 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4980, decls1)))
and encode_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____5002 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5002
       then
         let uu____5003 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5003
       else ());
      (let uu____5005 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5005 with
       | (vars,pat_term) ->
           let uu____5015 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5038  ->
                     fun v1  ->
                       match uu____5038 with
                       | (env1,vars1) ->
                           let uu____5066 = gen_term_var env1 v1 in
                           (match uu____5066 with
                            | (xx,uu____5078,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____5015 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5125 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5126 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5127 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5133 =
                        let uu____5136 = encode_const c in
                        (scrutinee, uu____5136) in
                      FStar_SMTEncoding_Util.mkEq uu____5133
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5155 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5155 with
                        | (uu____5159,uu____5160::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5162 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5183  ->
                                  match uu____5183 with
                                  | (arg,uu____5189) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5199 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5199)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5219) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5238 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5253 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5275  ->
                                  match uu____5275 with
                                  | (arg,uu____5284) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5294 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5294)) in
                      FStar_All.pipe_right uu____5253 FStar_List.flatten in
                let pat_term1 uu____5310 = encode_term pat_term env1 in
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
      let uu____5317 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5332  ->
                fun uu____5333  ->
                  match (uu____5332, uu____5333) with
                  | ((tms,decls),(t,uu____5353)) ->
                      let uu____5364 = encode_term t env in
                      (match uu____5364 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5317 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5398 = FStar_Syntax_Util.list_elements e in
        match uu____5398 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5416 =
          let uu____5426 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5426 FStar_Syntax_Util.head_and_args in
        match uu____5416 with
        | (head1,args) ->
            let uu____5457 =
              let uu____5465 =
                let uu____5466 = FStar_Syntax_Util.un_uinst head1 in
                uu____5466.FStar_Syntax_Syntax.n in
              (uu____5465, args) in
            (match uu____5457 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5480,uu____5481)::(e,uu____5483)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> (e, None)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5514)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpatT_lid
                 -> (e, None)
             | uu____5535 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or t1 =
          let uu____5568 =
            let uu____5578 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5578 FStar_Syntax_Util.head_and_args in
          match uu____5568 with
          | (head1,args) ->
              let uu____5607 =
                let uu____5615 =
                  let uu____5616 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5616.FStar_Syntax_Syntax.n in
                (uu____5615, args) in
              (match uu____5607 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5629)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5649 -> None) in
        match elts with
        | t1::[] ->
            let uu____5667 = smt_pat_or t1 in
            (match uu____5667 with
             | Some e ->
                 let uu____5683 = list_elements1 e in
                 FStar_All.pipe_right uu____5683
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5700 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5700
                           (FStar_List.map one_pat)))
             | uu____5714 ->
                 let uu____5718 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5718])
        | uu____5749 ->
            let uu____5751 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5751] in
      let uu____5782 =
        let uu____5798 =
          let uu____5799 = FStar_Syntax_Subst.compress t in
          uu____5799.FStar_Syntax_Syntax.n in
        match uu____5798 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5829 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5829 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5864;
                        FStar_Syntax_Syntax.effect_name = uu____5865;
                        FStar_Syntax_Syntax.result_typ = uu____5866;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5868)::(post,uu____5870)::(pats,uu____5872)::[];
                        FStar_Syntax_Syntax.flags = uu____5873;_}
                      ->
                      let uu____5905 = lemma_pats pats in
                      (binders1, pre, post, uu____5905)
                  | uu____5924 -> failwith "impos"))
        | uu____5940 -> failwith "Impos" in
      match uu____5782 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___138_5985 = env in
            {
              bindings = (uu___138_5985.bindings);
              depth = (uu___138_5985.depth);
              tcenv = (uu___138_5985.tcenv);
              warn = (uu___138_5985.warn);
              cache = (uu___138_5985.cache);
              nolabels = (uu___138_5985.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___138_5985.encode_non_total_function_typ);
              current_module_name = (uu___138_5985.current_module_name)
            } in
          let uu____5986 = encode_binders None binders env1 in
          (match uu____5986 with
           | (vars,guards,env2,decls,uu____6001) ->
               let uu____6008 =
                 let uu____6015 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____6046 =
                             let uu____6051 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun uu____6067  ->
                                       match uu____6067 with
                                       | (t1,uu____6074) ->
                                           encode_term t1 env2)) in
                             FStar_All.pipe_right uu____6051 FStar_List.unzip in
                           match uu____6046 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____6015 FStar_List.unzip in
               (match uu____6008 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___139_6124 = env2 in
                      {
                        bindings = (uu___139_6124.bindings);
                        depth = (uu___139_6124.depth);
                        tcenv = (uu___139_6124.tcenv);
                        warn = (uu___139_6124.warn);
                        cache = (uu___139_6124.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___139_6124.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___139_6124.encode_non_total_function_typ);
                        current_module_name =
                          (uu___139_6124.current_module_name)
                      } in
                    let uu____6125 =
                      let uu____6128 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6128 env3 in
                    (match uu____6125 with
                     | (pre1,decls'') ->
                         let uu____6133 =
                           let uu____6136 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6136 env3 in
                         (match uu____6133 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6143 =
                                let uu____6144 =
                                  let uu____6150 =
                                    let uu____6151 =
                                      let uu____6154 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6154, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6151 in
                                  (pats, vars, uu____6150) in
                                FStar_SMTEncoding_Util.mkForall uu____6144 in
                              (uu____6143, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6167 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6167
        then
          let uu____6168 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6169 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6168 uu____6169
        else () in
      let enc f r l =
        let uu____6196 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6209 = encode_term (fst x) env in
                 match uu____6209 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6196 with
        | (decls,args) ->
            let uu____6226 =
              let uu___140_6227 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_6227.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_6227.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6226, decls) in
      let const_op f r uu____6246 = let uu____6249 = f r in (uu____6249, []) in
      let un_op f l =
        let uu____6265 = FStar_List.hd l in FStar_All.pipe_left f uu____6265 in
      let bin_op f uu___112_6278 =
        match uu___112_6278 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6286 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6313 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6322  ->
                 match uu____6322 with
                 | (t,uu____6330) ->
                     let uu____6331 = encode_formula t env in
                     (match uu____6331 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6313 with
        | (decls,phis) ->
            let uu____6348 =
              let uu___141_6349 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___141_6349.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___141_6349.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6348, decls) in
      let eq_op r uu___113_6365 =
        match uu___113_6365 with
        | uu____6368::e1::e2::[] ->
            let uu____6399 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6399 r [e1; e2]
        | uu____6418::uu____6419::e1::e2::[] ->
            let uu____6458 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6458 r [e1; e2]
        | l ->
            let uu____6478 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6478 r l in
      let mk_imp1 r uu___114_6497 =
        match uu___114_6497 with
        | (lhs,uu____6501)::(rhs,uu____6503)::[] ->
            let uu____6524 = encode_formula rhs env in
            (match uu____6524 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6533) ->
                      (l1, decls1)
                  | uu____6536 ->
                      let uu____6537 = encode_formula lhs env in
                      (match uu____6537 with
                       | (l2,decls2) ->
                           let uu____6544 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6544, (FStar_List.append decls1 decls2)))))
        | uu____6546 -> failwith "impossible" in
      let mk_ite r uu___115_6561 =
        match uu___115_6561 with
        | (guard,uu____6565)::(_then,uu____6567)::(_else,uu____6569)::[] ->
            let uu____6598 = encode_formula guard env in
            (match uu____6598 with
             | (g,decls1) ->
                 let uu____6605 = encode_formula _then env in
                 (match uu____6605 with
                  | (t,decls2) ->
                      let uu____6612 = encode_formula _else env in
                      (match uu____6612 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6621 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6640 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6640 in
      let connectives =
        let uu____6652 =
          let uu____6661 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6661) in
        let uu____6674 =
          let uu____6684 =
            let uu____6693 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6693) in
          let uu____6706 =
            let uu____6716 =
              let uu____6726 =
                let uu____6735 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6735) in
              let uu____6748 =
                let uu____6758 =
                  let uu____6768 =
                    let uu____6777 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6777) in
                  [uu____6768;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6758 in
              uu____6726 :: uu____6748 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6716 in
          uu____6684 :: uu____6706 in
        uu____6652 :: uu____6674 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6939 = encode_formula phi' env in
            (match uu____6939 with
             | (phi2,decls) ->
                 let uu____6946 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6946, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6947 ->
            let uu____6952 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6952 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6981 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6981 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6989;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6991;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____7007 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____7007 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____7039::(x,uu____7041)::(t,uu____7043)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____7077 = encode_term x env in
                 (match uu____7077 with
                  | (x1,decls) ->
                      let uu____7084 = encode_term t env in
                      (match uu____7084 with
                       | (t1,decls') ->
                           let uu____7091 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____7091, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____7095)::(msg,uu____7097)::(phi2,uu____7099)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____7133 =
                   let uu____7136 =
                     let uu____7137 = FStar_Syntax_Subst.compress r in
                     uu____7137.FStar_Syntax_Syntax.n in
                   let uu____7140 =
                     let uu____7141 = FStar_Syntax_Subst.compress msg in
                     uu____7141.FStar_Syntax_Syntax.n in
                   (uu____7136, uu____7140) in
                 (match uu____7133 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7148))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____7164 -> fallback phi2)
             | uu____7167 when head_redex env head2 ->
                 let uu____7175 = whnf env phi1 in
                 encode_formula uu____7175 env
             | uu____7176 ->
                 let uu____7184 = encode_term phi1 env in
                 (match uu____7184 with
                  | (tt,decls) ->
                      let uu____7191 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___142_7192 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___142_7192.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___142_7192.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7191, decls)))
        | uu____7195 ->
            let uu____7196 = encode_term phi1 env in
            (match uu____7196 with
             | (tt,decls) ->
                 let uu____7203 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___143_7204 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___143_7204.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___143_7204.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7203, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7231 = encode_binders None bs env1 in
        match uu____7231 with
        | (vars,guards,env2,decls,uu____7253) ->
            let uu____7260 =
              let uu____7267 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7290 =
                          let uu____7295 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7309  ->
                                    match uu____7309 with
                                    | (t,uu____7315) ->
                                        encode_term t
                                          (let uu___144_7316 = env2 in
                                           {
                                             bindings =
                                               (uu___144_7316.bindings);
                                             depth = (uu___144_7316.depth);
                                             tcenv = (uu___144_7316.tcenv);
                                             warn = (uu___144_7316.warn);
                                             cache = (uu___144_7316.cache);
                                             nolabels =
                                               (uu___144_7316.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___144_7316.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___144_7316.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7295 FStar_List.unzip in
                        match uu____7290 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7267 FStar_List.unzip in
            (match uu____7260 with
             | (pats,decls') ->
                 let uu____7368 = encode_formula body env2 in
                 (match uu____7368 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7387;
                             FStar_SMTEncoding_Term.rng = uu____7388;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7396 -> guards in
                      let uu____7399 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7399, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7433  ->
                   match uu____7433 with
                   | (x,uu____7437) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7443 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7449 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7449) uu____7443 tl1 in
             let uu____7451 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7463  ->
                       match uu____7463 with
                       | (b,uu____7467) ->
                           let uu____7468 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7468)) in
             (match uu____7451 with
              | None  -> ()
              | Some (x,uu____7472) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7482 =
                    let uu____7483 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7483 in
                  FStar_Errors.warn pos uu____7482) in
       let uu____7484 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7484 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7490 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7526  ->
                     match uu____7526 with
                     | (l,uu____7536) -> FStar_Ident.lid_equals op l)) in
           (match uu____7490 with
            | None  -> fallback phi1
            | Some (uu____7559,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7588 = encode_q_body env vars pats body in
             match uu____7588 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7614 =
                     let uu____7620 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7620) in
                   FStar_SMTEncoding_Term.mkForall uu____7614
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7632 = encode_q_body env vars pats body in
             match uu____7632 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7657 =
                   let uu____7658 =
                     let uu____7664 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7664) in
                   FStar_SMTEncoding_Term.mkExists uu____7658
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7657, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7713 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7713 with
  | (asym,a) ->
      let uu____7718 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7718 with
       | (xsym,x) ->
           let uu____7723 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7723 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7753 =
                      let uu____7759 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____7759, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7753 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7774 =
                      let uu____7778 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7778) in
                    FStar_SMTEncoding_Util.mkApp uu____7774 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7786 =
                    let uu____7788 =
                      let uu____7790 =
                        let uu____7792 =
                          let uu____7793 =
                            let uu____7797 =
                              let uu____7798 =
                                let uu____7804 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7804) in
                              FStar_SMTEncoding_Util.mkForall uu____7798 in
                            (uu____7797, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7793 in
                        let uu____7813 =
                          let uu____7815 =
                            let uu____7816 =
                              let uu____7820 =
                                let uu____7821 =
                                  let uu____7827 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7827) in
                                FStar_SMTEncoding_Util.mkForall uu____7821 in
                              (uu____7820,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7816 in
                          [uu____7815] in
                        uu____7792 :: uu____7813 in
                      xtok_decl :: uu____7790 in
                    xname_decl :: uu____7788 in
                  (xtok1, uu____7786) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7876 =
                    let uu____7884 =
                      let uu____7890 =
                        let uu____7891 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7891 in
                      quant axy uu____7890 in
                    (FStar_Syntax_Const.op_Eq, uu____7884) in
                  let uu____7897 =
                    let uu____7906 =
                      let uu____7914 =
                        let uu____7920 =
                          let uu____7921 =
                            let uu____7922 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7922 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7921 in
                        quant axy uu____7920 in
                      (FStar_Syntax_Const.op_notEq, uu____7914) in
                    let uu____7928 =
                      let uu____7937 =
                        let uu____7945 =
                          let uu____7951 =
                            let uu____7952 =
                              let uu____7953 =
                                let uu____7956 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7957 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7956, uu____7957) in
                              FStar_SMTEncoding_Util.mkLT uu____7953 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7952 in
                          quant xy uu____7951 in
                        (FStar_Syntax_Const.op_LT, uu____7945) in
                      let uu____7963 =
                        let uu____7972 =
                          let uu____7980 =
                            let uu____7986 =
                              let uu____7987 =
                                let uu____7988 =
                                  let uu____7991 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7992 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7991, uu____7992) in
                                FStar_SMTEncoding_Util.mkLTE uu____7988 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7987 in
                            quant xy uu____7986 in
                          (FStar_Syntax_Const.op_LTE, uu____7980) in
                        let uu____7998 =
                          let uu____8007 =
                            let uu____8015 =
                              let uu____8021 =
                                let uu____8022 =
                                  let uu____8023 =
                                    let uu____8026 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____8027 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____8026, uu____8027) in
                                  FStar_SMTEncoding_Util.mkGT uu____8023 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____8022 in
                              quant xy uu____8021 in
                            (FStar_Syntax_Const.op_GT, uu____8015) in
                          let uu____8033 =
                            let uu____8042 =
                              let uu____8050 =
                                let uu____8056 =
                                  let uu____8057 =
                                    let uu____8058 =
                                      let uu____8061 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____8062 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____8061, uu____8062) in
                                    FStar_SMTEncoding_Util.mkGTE uu____8058 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____8057 in
                                quant xy uu____8056 in
                              (FStar_Syntax_Const.op_GTE, uu____8050) in
                            let uu____8068 =
                              let uu____8077 =
                                let uu____8085 =
                                  let uu____8091 =
                                    let uu____8092 =
                                      let uu____8093 =
                                        let uu____8096 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____8097 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____8096, uu____8097) in
                                      FStar_SMTEncoding_Util.mkSub uu____8093 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8092 in
                                  quant xy uu____8091 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____8085) in
                              let uu____8103 =
                                let uu____8112 =
                                  let uu____8120 =
                                    let uu____8126 =
                                      let uu____8127 =
                                        let uu____8128 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8128 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8127 in
                                    quant qx uu____8126 in
                                  (FStar_Syntax_Const.op_Minus, uu____8120) in
                                let uu____8134 =
                                  let uu____8143 =
                                    let uu____8151 =
                                      let uu____8157 =
                                        let uu____8158 =
                                          let uu____8159 =
                                            let uu____8162 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8163 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8162, uu____8163) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8159 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8158 in
                                      quant xy uu____8157 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8151) in
                                  let uu____8169 =
                                    let uu____8178 =
                                      let uu____8186 =
                                        let uu____8192 =
                                          let uu____8193 =
                                            let uu____8194 =
                                              let uu____8197 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8198 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8197, uu____8198) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8194 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8193 in
                                        quant xy uu____8192 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8186) in
                                    let uu____8204 =
                                      let uu____8213 =
                                        let uu____8221 =
                                          let uu____8227 =
                                            let uu____8228 =
                                              let uu____8229 =
                                                let uu____8232 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8233 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8232, uu____8233) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8229 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8228 in
                                          quant xy uu____8227 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8221) in
                                      let uu____8239 =
                                        let uu____8248 =
                                          let uu____8256 =
                                            let uu____8262 =
                                              let uu____8263 =
                                                let uu____8264 =
                                                  let uu____8267 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8268 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8267, uu____8268) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8264 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8263 in
                                            quant xy uu____8262 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8256) in
                                        let uu____8274 =
                                          let uu____8283 =
                                            let uu____8291 =
                                              let uu____8297 =
                                                let uu____8298 =
                                                  let uu____8299 =
                                                    let uu____8302 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8303 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8302, uu____8303) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8299 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8298 in
                                              quant xy uu____8297 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8291) in
                                          let uu____8309 =
                                            let uu____8318 =
                                              let uu____8326 =
                                                let uu____8332 =
                                                  let uu____8333 =
                                                    let uu____8334 =
                                                      let uu____8337 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8338 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8337,
                                                        uu____8338) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8334 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8333 in
                                                quant xy uu____8332 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8326) in
                                            let uu____8344 =
                                              let uu____8353 =
                                                let uu____8361 =
                                                  let uu____8367 =
                                                    let uu____8368 =
                                                      let uu____8369 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8369 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8368 in
                                                  quant qx uu____8367 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8361) in
                                              [uu____8353] in
                                            uu____8318 :: uu____8344 in
                                          uu____8283 :: uu____8309 in
                                        uu____8248 :: uu____8274 in
                                      uu____8213 :: uu____8239 in
                                    uu____8178 :: uu____8204 in
                                  uu____8143 :: uu____8169 in
                                uu____8112 :: uu____8134 in
                              uu____8077 :: uu____8103 in
                            uu____8042 :: uu____8068 in
                          uu____8007 :: uu____8033 in
                        uu____7972 :: uu____7998 in
                      uu____7937 :: uu____7963 in
                    uu____7906 :: uu____7928 in
                  uu____7876 :: uu____7897 in
                let mk1 l v1 =
                  let uu____8497 =
                    let uu____8502 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8534  ->
                              match uu____8534 with
                              | (l',uu____8543) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8502
                      (FStar_Option.map
                         (fun uu____8576  ->
                            match uu____8576 with | (uu____8587,b) -> b v1)) in
                  FStar_All.pipe_right uu____8497 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8628  ->
                          match uu____8628 with
                          | (l',uu____8637) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8663 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8663 with
        | (xxsym,xx) ->
            let uu____8668 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8668 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8676 =
                   let uu____8680 =
                     let uu____8681 =
                       let uu____8687 =
                         let uu____8688 =
                           let uu____8691 =
                             let uu____8692 =
                               let uu____8695 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8695) in
                             FStar_SMTEncoding_Util.mkEq uu____8692 in
                           (xx_has_type, uu____8691) in
                         FStar_SMTEncoding_Util.mkImp uu____8688 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8687) in
                     FStar_SMTEncoding_Util.mkForall uu____8681 in
                   let uu____8708 =
                     let uu____8709 =
                       let uu____8710 =
                         let uu____8711 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8711 in
                       Prims.strcat module_name uu____8710 in
                     varops.mk_unique uu____8709 in
                   (uu____8680, (Some "pretyping"), uu____8708) in
                 FStar_SMTEncoding_Util.mkAssume uu____8676)
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
    let uu____8741 =
      let uu____8742 =
        let uu____8746 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8746, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8742 in
    let uu____8748 =
      let uu____8750 =
        let uu____8751 =
          let uu____8755 =
            let uu____8756 =
              let uu____8762 =
                let uu____8763 =
                  let uu____8766 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8766) in
                FStar_SMTEncoding_Util.mkImp uu____8763 in
              ([[typing_pred]], [xx], uu____8762) in
            mkForall_fuel uu____8756 in
          (uu____8755, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8751 in
      [uu____8750] in
    uu____8741 :: uu____8748 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8794 =
      let uu____8795 =
        let uu____8799 =
          let uu____8800 =
            let uu____8806 =
              let uu____8809 =
                let uu____8811 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8811] in
              [uu____8809] in
            let uu____8814 =
              let uu____8815 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8815 tt in
            (uu____8806, [bb], uu____8814) in
          FStar_SMTEncoding_Util.mkForall uu____8800 in
        (uu____8799, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8795 in
    let uu____8826 =
      let uu____8828 =
        let uu____8829 =
          let uu____8833 =
            let uu____8834 =
              let uu____8840 =
                let uu____8841 =
                  let uu____8844 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8844) in
                FStar_SMTEncoding_Util.mkImp uu____8841 in
              ([[typing_pred]], [xx], uu____8840) in
            mkForall_fuel uu____8834 in
          (uu____8833, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8829 in
      [uu____8828] in
    uu____8794 :: uu____8826 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8878 =
        let uu____8879 =
          let uu____8883 =
            let uu____8885 =
              let uu____8887 =
                let uu____8889 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8890 =
                  let uu____8892 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8892] in
                uu____8889 :: uu____8890 in
              tt :: uu____8887 in
            tt :: uu____8885 in
          ("Prims.Precedes", uu____8883) in
        FStar_SMTEncoding_Util.mkApp uu____8879 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8878 in
    let precedes_y_x =
      let uu____8895 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8895 in
    let uu____8897 =
      let uu____8898 =
        let uu____8902 =
          let uu____8903 =
            let uu____8909 =
              let uu____8912 =
                let uu____8914 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8914] in
              [uu____8912] in
            let uu____8917 =
              let uu____8918 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8918 tt in
            (uu____8909, [bb], uu____8917) in
          FStar_SMTEncoding_Util.mkForall uu____8903 in
        (uu____8902, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8898 in
    let uu____8929 =
      let uu____8931 =
        let uu____8932 =
          let uu____8936 =
            let uu____8937 =
              let uu____8943 =
                let uu____8944 =
                  let uu____8947 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8947) in
                FStar_SMTEncoding_Util.mkImp uu____8944 in
              ([[typing_pred]], [xx], uu____8943) in
            mkForall_fuel uu____8937 in
          (uu____8936, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8932 in
      let uu____8960 =
        let uu____8962 =
          let uu____8963 =
            let uu____8967 =
              let uu____8968 =
                let uu____8974 =
                  let uu____8975 =
                    let uu____8978 =
                      let uu____8979 =
                        let uu____8981 =
                          let uu____8983 =
                            let uu____8985 =
                              let uu____8986 =
                                let uu____8989 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8990 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8989, uu____8990) in
                              FStar_SMTEncoding_Util.mkGT uu____8986 in
                            let uu____8991 =
                              let uu____8993 =
                                let uu____8994 =
                                  let uu____8997 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8998 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8997, uu____8998) in
                                FStar_SMTEncoding_Util.mkGTE uu____8994 in
                              let uu____8999 =
                                let uu____9001 =
                                  let uu____9002 =
                                    let uu____9005 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____9006 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____9005, uu____9006) in
                                  FStar_SMTEncoding_Util.mkLT uu____9002 in
                                [uu____9001] in
                              uu____8993 :: uu____8999 in
                            uu____8985 :: uu____8991 in
                          typing_pred_y :: uu____8983 in
                        typing_pred :: uu____8981 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8979 in
                    (uu____8978, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8975 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8974) in
              mkForall_fuel uu____8968 in
            (uu____8967, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8963 in
        [uu____8962] in
      uu____8931 :: uu____8960 in
    uu____8897 :: uu____8929 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9036 =
      let uu____9037 =
        let uu____9041 =
          let uu____9042 =
            let uu____9048 =
              let uu____9051 =
                let uu____9053 = FStar_SMTEncoding_Term.boxString b in
                [uu____9053] in
              [uu____9051] in
            let uu____9056 =
              let uu____9057 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____9057 tt in
            (uu____9048, [bb], uu____9056) in
          FStar_SMTEncoding_Util.mkForall uu____9042 in
        (uu____9041, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9037 in
    let uu____9068 =
      let uu____9070 =
        let uu____9071 =
          let uu____9075 =
            let uu____9076 =
              let uu____9082 =
                let uu____9083 =
                  let uu____9086 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____9086) in
                FStar_SMTEncoding_Util.mkImp uu____9083 in
              ([[typing_pred]], [xx], uu____9082) in
            mkForall_fuel uu____9076 in
          (uu____9075, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9071 in
      [uu____9070] in
    uu____9036 :: uu____9068 in
  let mk_ref1 env reft_name uu____9108 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____9119 =
        let uu____9123 =
          let uu____9125 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9125] in
        (reft_name, uu____9123) in
      FStar_SMTEncoding_Util.mkApp uu____9119 in
    let refb =
      let uu____9128 =
        let uu____9132 =
          let uu____9134 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9134] in
        (reft_name, uu____9132) in
      FStar_SMTEncoding_Util.mkApp uu____9128 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9138 =
      let uu____9139 =
        let uu____9143 =
          let uu____9144 =
            let uu____9150 =
              let uu____9151 =
                let uu____9154 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9154) in
              FStar_SMTEncoding_Util.mkImp uu____9151 in
            ([[typing_pred]], [xx; aa], uu____9150) in
          mkForall_fuel uu____9144 in
        (uu____9143, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9139 in
    [uu____9138] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9194 =
      let uu____9195 =
        let uu____9199 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9199, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9195 in
    [uu____9194] in
  let mk_and_interp env conj uu____9210 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9227 =
      let uu____9228 =
        let uu____9232 =
          let uu____9233 =
            let uu____9239 =
              let uu____9240 =
                let uu____9243 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9243, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9240 in
            ([[l_and_a_b]], [aa; bb], uu____9239) in
          FStar_SMTEncoding_Util.mkForall uu____9233 in
        (uu____9232, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9228 in
    [uu____9227] in
  let mk_or_interp env disj uu____9267 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9284 =
      let uu____9285 =
        let uu____9289 =
          let uu____9290 =
            let uu____9296 =
              let uu____9297 =
                let uu____9300 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9300, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9297 in
            ([[l_or_a_b]], [aa; bb], uu____9296) in
          FStar_SMTEncoding_Util.mkForall uu____9290 in
        (uu____9289, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9285 in
    [uu____9284] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9341 =
      let uu____9342 =
        let uu____9346 =
          let uu____9347 =
            let uu____9353 =
              let uu____9354 =
                let uu____9357 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9357, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9354 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9353) in
          FStar_SMTEncoding_Util.mkForall uu____9347 in
        (uu____9346, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9342 in
    [uu____9341] in
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
    let uu____9404 =
      let uu____9405 =
        let uu____9409 =
          let uu____9410 =
            let uu____9416 =
              let uu____9417 =
                let uu____9420 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9420, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9417 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9416) in
          FStar_SMTEncoding_Util.mkForall uu____9410 in
        (uu____9409, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9405 in
    [uu____9404] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9465 =
      let uu____9466 =
        let uu____9470 =
          let uu____9471 =
            let uu____9477 =
              let uu____9478 =
                let uu____9481 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9481, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9478 in
            ([[l_imp_a_b]], [aa; bb], uu____9477) in
          FStar_SMTEncoding_Util.mkForall uu____9471 in
        (uu____9470, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9466 in
    [uu____9465] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9522 =
      let uu____9523 =
        let uu____9527 =
          let uu____9528 =
            let uu____9534 =
              let uu____9535 =
                let uu____9538 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9538, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9535 in
            ([[l_iff_a_b]], [aa; bb], uu____9534) in
          FStar_SMTEncoding_Util.mkForall uu____9528 in
        (uu____9527, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9523 in
    [uu____9522] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9572 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9572 in
    let uu____9574 =
      let uu____9575 =
        let uu____9579 =
          let uu____9580 =
            let uu____9586 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9586) in
          FStar_SMTEncoding_Util.mkForall uu____9580 in
        (uu____9579, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9575 in
    [uu____9574] in
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
      let uu____9626 =
        let uu____9630 =
          let uu____9632 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9632] in
        ("Valid", uu____9630) in
      FStar_SMTEncoding_Util.mkApp uu____9626 in
    let uu____9634 =
      let uu____9635 =
        let uu____9639 =
          let uu____9640 =
            let uu____9646 =
              let uu____9647 =
                let uu____9650 =
                  let uu____9651 =
                    let uu____9657 =
                      let uu____9660 =
                        let uu____9662 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9662] in
                      [uu____9660] in
                    let uu____9665 =
                      let uu____9666 =
                        let uu____9669 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9669, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9666 in
                    (uu____9657, [xx1], uu____9665) in
                  FStar_SMTEncoding_Util.mkForall uu____9651 in
                (uu____9650, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9647 in
            ([[l_forall_a_b]], [aa; bb], uu____9646) in
          FStar_SMTEncoding_Util.mkForall uu____9640 in
        (uu____9639, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9635 in
    [uu____9634] in
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
      let uu____9720 =
        let uu____9724 =
          let uu____9726 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9726] in
        ("Valid", uu____9724) in
      FStar_SMTEncoding_Util.mkApp uu____9720 in
    let uu____9728 =
      let uu____9729 =
        let uu____9733 =
          let uu____9734 =
            let uu____9740 =
              let uu____9741 =
                let uu____9744 =
                  let uu____9745 =
                    let uu____9751 =
                      let uu____9754 =
                        let uu____9756 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9756] in
                      [uu____9754] in
                    let uu____9759 =
                      let uu____9760 =
                        let uu____9763 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9763, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9760 in
                    (uu____9751, [xx1], uu____9759) in
                  FStar_SMTEncoding_Util.mkExists uu____9745 in
                (uu____9744, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9741 in
            ([[l_exists_a_b]], [aa; bb], uu____9740) in
          FStar_SMTEncoding_Util.mkForall uu____9734 in
        (uu____9733, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9729 in
    [uu____9728] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9799 =
      let uu____9800 =
        let uu____9804 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9805 = varops.mk_unique "typing_range_const" in
        (uu____9804, (Some "Range_const typing"), uu____9805) in
      FStar_SMTEncoding_Util.mkAssume uu____9800 in
    [uu____9799] in
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
          let uu____10067 =
            FStar_Util.find_opt
              (fun uu____10085  ->
                 match uu____10085 with
                 | (l,uu____10095) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____10067 with
          | None  -> []
          | Some (uu____10117,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10154 = encode_function_type_as_formula t env in
        match uu____10154 with
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
            let uu____10186 =
              (let uu____10187 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10187) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10186
            then
              let uu____10191 = new_term_constant_and_tok_from_lid env lid in
              match uu____10191 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10203 =
                      let uu____10204 = FStar_Syntax_Subst.compress t_norm in
                      uu____10204.FStar_Syntax_Syntax.n in
                    match uu____10203 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10209) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10226  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10229 -> [] in
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
              (let uu____10238 = prims.is lid in
               if uu____10238
               then
                 let vname = varops.new_fvar lid in
                 let uu____10243 = prims.mk lid vname in
                 match uu____10243 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10258 =
                    let uu____10264 = curried_arrow_formals_comp t_norm in
                    match uu____10264 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10275 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10275
                          then
                            let uu____10276 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___145_10277 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___145_10277.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___145_10277.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___145_10277.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___145_10277.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___145_10277.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___145_10277.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___145_10277.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___145_10277.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___145_10277.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___145_10277.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___145_10277.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___145_10277.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___145_10277.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___145_10277.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___145_10277.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___145_10277.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___145_10277.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___145_10277.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___145_10277.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___145_10277.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___145_10277.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___145_10277.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___145_10277.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___145_10277.FStar_TypeChecker_Env.proof_ns)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10276
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10284 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10284)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10258 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10311 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10311 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10324 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___116_10348  ->
                                     match uu___116_10348 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10351 =
                                           FStar_Util.prefix vars in
                                         (match uu____10351 with
                                          | (uu____10362,(xxsym,uu____10364))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10374 =
                                                let uu____10375 =
                                                  let uu____10379 =
                                                    let uu____10380 =
                                                      let uu____10386 =
                                                        let uu____10387 =
                                                          let uu____10390 =
                                                            let uu____10391 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10391 in
                                                          (vapp, uu____10390) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10387 in
                                                      ([[vapp]], vars,
                                                        uu____10386) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10380 in
                                                  (uu____10379,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10375 in
                                              [uu____10374])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10402 =
                                           FStar_Util.prefix vars in
                                         (match uu____10402 with
                                          | (uu____10413,(xxsym,uu____10415))
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
                                              let uu____10429 =
                                                let uu____10430 =
                                                  let uu____10434 =
                                                    let uu____10435 =
                                                      let uu____10441 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10441) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10435 in
                                                  (uu____10434,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10430 in
                                              [uu____10429])
                                     | uu____10450 -> [])) in
                           let uu____10451 = encode_binders None formals env1 in
                           (match uu____10451 with
                            | (vars,guards,env',decls1,uu____10467) ->
                                let uu____10474 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10479 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10479, decls1)
                                  | Some p ->
                                      let uu____10481 = encode_formula p env' in
                                      (match uu____10481 with
                                       | (g,ds) ->
                                           let uu____10488 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10488,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10474 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10497 =
                                         let uu____10501 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10501) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10497 in
                                     let uu____10506 =
                                       let vname_decl =
                                         let uu____10511 =
                                           let uu____10517 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10522  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10517,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10511 in
                                       let uu____10527 =
                                         let env2 =
                                           let uu___146_10531 = env1 in
                                           {
                                             bindings =
                                               (uu___146_10531.bindings);
                                             depth = (uu___146_10531.depth);
                                             tcenv = (uu___146_10531.tcenv);
                                             warn = (uu___146_10531.warn);
                                             cache = (uu___146_10531.cache);
                                             nolabels =
                                               (uu___146_10531.nolabels);
                                             use_zfuel_name =
                                               (uu___146_10531.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___146_10531.current_module_name)
                                           } in
                                         let uu____10532 =
                                           let uu____10533 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10533 in
                                         if uu____10532
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10527 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10543::uu____10544 ->
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
                                                   let uu____10567 =
                                                     let uu____10573 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10573) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10567 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10587 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10589 =
                                             match formals with
                                             | [] ->
                                                 let uu____10598 =
                                                   let uu____10599 =
                                                     let uu____10601 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10601 in
                                                   push_free_var env1 lid
                                                     vname uu____10599 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10598)
                                             | uu____10604 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10609 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10609 in
                                                 let name_tok_corr =
                                                   let uu____10611 =
                                                     let uu____10615 =
                                                       let uu____10616 =
                                                         let uu____10622 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10622) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10616 in
                                                     (uu____10615,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10611 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10589 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10506 with
                                      | (decls2,env2) ->
                                          let uu____10646 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10651 =
                                              encode_term res_t1 env' in
                                            match uu____10651 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10659 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10659,
                                                  decls) in
                                          (match uu____10646 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10667 =
                                                   let uu____10671 =
                                                     let uu____10672 =
                                                       let uu____10678 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10678) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10672 in
                                                   (uu____10671,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10667 in
                                               let freshness =
                                                 let uu____10687 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10687
                                                 then
                                                   let uu____10690 =
                                                     let uu____10691 =
                                                       let uu____10697 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
                                                       let uu____10703 =
                                                         varops.next_id () in
                                                       (vname, uu____10697,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10703) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10691 in
                                                   let uu____10705 =
                                                     let uu____10707 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10707] in
                                                   uu____10690 :: uu____10705
                                                 else [] in
                                               let g =
                                                 let uu____10711 =
                                                   let uu____10713 =
                                                     let uu____10715 =
                                                       let uu____10717 =
                                                         let uu____10719 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10719 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10717 in
                                                     FStar_List.append decls3
                                                       uu____10715 in
                                                   FStar_List.append decls2
                                                     uu____10713 in
                                                 FStar_List.append decls11
                                                   uu____10711 in
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
          let uu____10741 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10741 with
          | None  ->
              let uu____10764 = encode_free_var env x t t_norm [] in
              (match uu____10764 with
               | (decls,env1) ->
                   let uu____10779 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10779 with
                    | (n1,x',uu____10798) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10810) -> ((n1, x1), [], env)
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
          let uu____10843 = encode_free_var env lid t tt quals in
          match uu____10843 with
          | (decls,env1) ->
              let uu____10854 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10854
              then
                let uu____10858 =
                  let uu____10860 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10860 in
                (uu____10858, env1)
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
             (fun uu____10888  ->
                fun lb  ->
                  match uu____10888 with
                  | (decls,env1) ->
                      let uu____10900 =
                        let uu____10904 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10904
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10900 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10918 = FStar_Syntax_Util.head_and_args t in
    match uu____10918 with
    | (hd1,args) ->
        let uu____10944 =
          let uu____10945 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10945.FStar_Syntax_Syntax.n in
        (match uu____10944 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10949,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10962 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10977  ->
      fun quals  ->
        match uu____10977 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____11026 = FStar_Util.first_N nbinders formals in
              match uu____11026 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11066  ->
                         fun uu____11067  ->
                           match (uu____11066, uu____11067) with
                           | ((formal,uu____11077),(binder,uu____11079)) ->
                               let uu____11084 =
                                 let uu____11089 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11089) in
                               FStar_Syntax_Syntax.NT uu____11084) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11094 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11108  ->
                              match uu____11108 with
                              | (x,i) ->
                                  let uu____11115 =
                                    let uu___147_11116 = x in
                                    let uu____11117 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___147_11116.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___147_11116.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11117
                                    } in
                                  (uu____11115, i))) in
                    FStar_All.pipe_right uu____11094
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11129 =
                      let uu____11131 =
                        let uu____11132 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11132.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____11131 in
                    let uu____11136 =
                      let uu____11137 = FStar_Syntax_Subst.compress body in
                      let uu____11138 =
                        let uu____11139 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11139 in
                      FStar_Syntax_Syntax.extend_app_n uu____11137
                        uu____11138 in
                    uu____11136 uu____11129 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11181 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11181
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___148_11182 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___148_11182.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___148_11182.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___148_11182.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___148_11182.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___148_11182.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___148_11182.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___148_11182.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___148_11182.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___148_11182.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___148_11182.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___148_11182.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___148_11182.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___148_11182.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___148_11182.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___148_11182.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___148_11182.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___148_11182.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___148_11182.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___148_11182.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___148_11182.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___148_11182.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___148_11182.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___148_11182.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___148_11182.FStar_TypeChecker_Env.proof_ns)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11203 = FStar_Syntax_Util.abs_formals e in
                match uu____11203 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11252::uu____11253 ->
                         let uu____11261 =
                           let uu____11262 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11262.FStar_Syntax_Syntax.n in
                         (match uu____11261 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11289 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11289 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11315 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11315
                                   then
                                     let uu____11333 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11333 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11379  ->
                                                   fun uu____11380  ->
                                                     match (uu____11379,
                                                             uu____11380)
                                                     with
                                                     | ((x,uu____11390),
                                                        (b,uu____11392)) ->
                                                         let uu____11397 =
                                                           let uu____11402 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11402) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11397)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11404 =
                                            let uu____11415 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11415) in
                                          (uu____11404, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11450 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11450 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11502) ->
                              let uu____11507 =
                                let uu____11518 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____11518 in
                              (uu____11507, true)
                          | uu____11551 when Prims.op_Negation norm1 ->
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
                          | uu____11553 ->
                              let uu____11554 =
                                let uu____11555 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11556 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11555
                                  uu____11556 in
                              failwith uu____11554)
                     | uu____11569 ->
                         let uu____11570 =
                           let uu____11571 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11571.FStar_Syntax_Syntax.n in
                         (match uu____11570 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11598 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11598 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11616 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11616 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11664 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11692 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11692
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11699 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11740  ->
                            fun lb  ->
                              match uu____11740 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11791 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11791
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11794 =
                                      let uu____11802 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11802
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11794 with
                                    | (tok,decl,env2) ->
                                        let uu____11827 =
                                          let uu____11834 =
                                            let uu____11840 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11840, tok) in
                                          uu____11834 :: toks in
                                        (uu____11827, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11699 with
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
                        | uu____11942 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11947 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11947 vars)
                            else
                              (let uu____11949 =
                                 let uu____11953 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11953) in
                               FStar_SMTEncoding_Util.mkApp uu____11949) in
                      let uu____11958 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___117_11960  ->
                                 match uu___117_11960 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11961 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11964 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11964))) in
                      if uu____11958
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11984;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11986;
                                FStar_Syntax_Syntax.lbeff = uu____11987;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____12028 =
                                 let uu____12032 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____12032 with
                                 | (tcenv',uu____12043,e_t) ->
                                     let uu____12047 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12054 -> failwith "Impossible" in
                                     (match uu____12047 with
                                      | (e1,t_norm1) ->
                                          ((let uu___151_12063 = env1 in
                                            {
                                              bindings =
                                                (uu___151_12063.bindings);
                                              depth = (uu___151_12063.depth);
                                              tcenv = tcenv';
                                              warn = (uu___151_12063.warn);
                                              cache = (uu___151_12063.cache);
                                              nolabels =
                                                (uu___151_12063.nolabels);
                                              use_zfuel_name =
                                                (uu___151_12063.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___151_12063.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___151_12063.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____12028 with
                                | (env',e1,t_norm1) ->
                                    let uu____12070 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____12070 with
                                     | ((binders,body,uu____12082,uu____12083),curry)
                                         ->
                                         ((let uu____12090 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____12090
                                           then
                                             let uu____12091 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12092 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12091 uu____12092
                                           else ());
                                          (let uu____12094 =
                                             encode_binders None binders env' in
                                           match uu____12094 with
                                           | (vars,guards,env'1,binder_decls,uu____12110)
                                               ->
                                               let body1 =
                                                 let uu____12118 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12118
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12121 =
                                                 let uu____12126 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12126
                                                 then
                                                   let uu____12132 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12133 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12132, uu____12133)
                                                 else
                                                   (let uu____12139 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12139)) in
                                               (match uu____12121 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12153 =
                                                        let uu____12157 =
                                                          let uu____12158 =
                                                            let uu____12164 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12164) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12158 in
                                                        let uu____12170 =
                                                          let uu____12172 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12172 in
                                                        (uu____12157,
                                                          uu____12170,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12153 in
                                                    let uu____12174 =
                                                      let uu____12176 =
                                                        let uu____12178 =
                                                          let uu____12180 =
                                                            let uu____12182 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12182 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12180 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12178 in
                                                      FStar_List.append
                                                        decls1 uu____12176 in
                                                    (uu____12174, env1))))))
                           | uu____12185 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12204 = varops.fresh "fuel" in
                             (uu____12204, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12207 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12246  ->
                                     fun uu____12247  ->
                                       match (uu____12246, uu____12247) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12329 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12329 in
                                           let gtok =
                                             let uu____12331 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12331 in
                                           let env3 =
                                             let uu____12333 =
                                               let uu____12335 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12335 in
                                             push_free_var env2 flid gtok
                                               uu____12333 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12207 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12421
                                 t_norm uu____12423 =
                                 match (uu____12421, uu____12423) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12450;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12451;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12468 =
                                       let uu____12472 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12472 with
                                       | (tcenv',uu____12487,e_t) ->
                                           let uu____12491 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12498 ->
                                                 failwith "Impossible" in
                                           (match uu____12491 with
                                            | (e1,t_norm1) ->
                                                ((let uu___152_12507 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___152_12507.bindings);
                                                    depth =
                                                      (uu___152_12507.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___152_12507.warn);
                                                    cache =
                                                      (uu___152_12507.cache);
                                                    nolabels =
                                                      (uu___152_12507.nolabels);
                                                    use_zfuel_name =
                                                      (uu___152_12507.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___152_12507.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___152_12507.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12468 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12517 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12517
                                            then
                                              let uu____12518 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12519 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12520 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12518 uu____12519
                                                uu____12520
                                            else ());
                                           (let uu____12522 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12522 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12544 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12544
                                                  then
                                                    let uu____12545 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12546 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12547 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12548 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12545 uu____12546
                                                      uu____12547 uu____12548
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12552 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12552 with
                                                  | (vars,guards,env'1,binder_decls,uu____12570)
                                                      ->
                                                      let decl_g =
                                                        let uu____12578 =
                                                          let uu____12584 =
                                                            let uu____12586 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12586 in
                                                          (g, uu____12584,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12578 in
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
                                                        let uu____12601 =
                                                          let uu____12605 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12605) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12601 in
                                                      let gsapp =
                                                        let uu____12611 =
                                                          let uu____12615 =
                                                            let uu____12617 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12617 ::
                                                              vars_tm in
                                                          (g, uu____12615) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12611 in
                                                      let gmax =
                                                        let uu____12621 =
                                                          let uu____12625 =
                                                            let uu____12627 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12627 ::
                                                              vars_tm in
                                                          (g, uu____12625) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12621 in
                                                      let body1 =
                                                        let uu____12631 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12631
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12633 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12633 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12644
                                                               =
                                                               let uu____12648
                                                                 =
                                                                 let uu____12649
                                                                   =
                                                                   let uu____12657
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
                                                                    uu____12657) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12649 in
                                                               let uu____12668
                                                                 =
                                                                 let uu____12670
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12670 in
                                                               (uu____12648,
                                                                 uu____12668,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12644 in
                                                           let eqn_f =
                                                             let uu____12673
                                                               =
                                                               let uu____12677
                                                                 =
                                                                 let uu____12678
                                                                   =
                                                                   let uu____12684
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12684) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12678 in
                                                               (uu____12677,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12673 in
                                                           let eqn_g' =
                                                             let uu____12692
                                                               =
                                                               let uu____12696
                                                                 =
                                                                 let uu____12697
                                                                   =
                                                                   let uu____12703
                                                                    =
                                                                    let uu____12704
                                                                    =
                                                                    let uu____12707
                                                                    =
                                                                    let uu____12708
                                                                    =
                                                                    let uu____12712
                                                                    =
                                                                    let uu____12714
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12714
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12712) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12708 in
                                                                    (gsapp,
                                                                    uu____12707) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12704 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12703) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12697 in
                                                               (uu____12696,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12692 in
                                                           let uu____12726 =
                                                             let uu____12731
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12731
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12748)
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
                                                                    let uu____12763
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12763
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12766
                                                                    =
                                                                    let uu____12770
                                                                    =
                                                                    let uu____12771
                                                                    =
                                                                    let uu____12777
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12777) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12771 in
                                                                    (uu____12770,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12766 in
                                                                 let uu____12788
                                                                   =
                                                                   let uu____12792
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12792
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12800
                                                                    =
                                                                    let uu____12802
                                                                    =
                                                                    let uu____12803
                                                                    =
                                                                    let uu____12807
                                                                    =
                                                                    let uu____12808
                                                                    =
                                                                    let uu____12814
                                                                    =
                                                                    let uu____12815
                                                                    =
                                                                    let uu____12818
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12818,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12815 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12814) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12808 in
                                                                    (uu____12807,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12803 in
                                                                    [uu____12802] in
                                                                    (d3,
                                                                    uu____12800) in
                                                                 (match uu____12788
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12726
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
                               let uu____12853 =
                                 let uu____12860 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12896  ->
                                      fun uu____12897  ->
                                        match (uu____12896, uu____12897) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12983 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12983 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12860 in
                               (match uu____12853 with
                                | (decls2,eqns,env01) ->
                                    let uu____13023 =
                                      let isDeclFun uu___118_13031 =
                                        match uu___118_13031 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____13032 -> true
                                        | uu____13038 -> false in
                                      let uu____13039 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____13039
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____13023 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____13066 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____13066
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
        let uu____13099 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13099 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____13102 = encode_sigelt' env se in
      match uu____13102 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13112 =
                  let uu____13113 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13113 in
                [uu____13112]
            | uu____13114 ->
                let uu____13115 =
                  let uu____13117 =
                    let uu____13118 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13118 in
                  uu____13117 :: g in
                let uu____13119 =
                  let uu____13121 =
                    let uu____13122 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13122 in
                  [uu____13121] in
                FStar_List.append uu____13115 uu____13119 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13130 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13133 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13135 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13137 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13145 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13148 =
            let uu____13149 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13149 Prims.op_Negation in
          if uu____13148
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13169 ->
                   let uu____13170 =
                     let uu____13173 =
                       let uu____13174 =
                         let uu____13189 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13189) in
                       FStar_Syntax_Syntax.Tm_abs uu____13174 in
                     FStar_Syntax_Syntax.mk uu____13173 in
                   uu____13170 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13242 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13242 with
               | (aname,atok,env2) ->
                   let uu____13252 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13252 with
                    | (formals,uu____13262) ->
                        let uu____13269 =
                          let uu____13272 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13272 env2 in
                        (match uu____13269 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13280 =
                                 let uu____13281 =
                                   let uu____13287 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13295  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13287,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13281 in
                               [uu____13280;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13302 =
                               let aux uu____13331 uu____13332 =
                                 match (uu____13331, uu____13332) with
                                 | ((bv,uu____13359),(env3,acc_sorts,acc)) ->
                                     let uu____13380 = gen_term_var env3 bv in
                                     (match uu____13380 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13302 with
                              | (uu____13418,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13432 =
                                      let uu____13436 =
                                        let uu____13437 =
                                          let uu____13443 =
                                            let uu____13444 =
                                              let uu____13447 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13447) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13444 in
                                          ([[app]], xs_sorts, uu____13443) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13437 in
                                      (uu____13436, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13432 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13459 =
                                      let uu____13463 =
                                        let uu____13464 =
                                          let uu____13470 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13470) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13464 in
                                      (uu____13463,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13459 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13480 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13480 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13496,uu____13497)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13498 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13498 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13509,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13514 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___119_13516  ->
                      match uu___119_13516 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13517 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13520 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13521 -> false)) in
            Prims.op_Negation uu____13514 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13527 = encode_top_level_val env fv t quals in
             match uu____13527 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13539 =
                   let uu____13541 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13541 in
                 (uu____13539, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13546 = encode_formula f env in
          (match uu____13546 with
           | (f1,decls) ->
               let g =
                 let uu____13555 =
                   let uu____13556 =
                     let uu____13560 =
                       let uu____13562 =
                         let uu____13563 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13563 in
                       Some uu____13562 in
                     let uu____13564 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13560, uu____13564) in
                   FStar_SMTEncoding_Util.mkAssume uu____13556 in
                 [uu____13555] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13568,uu____13569) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13575 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13582 =
                       let uu____13587 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13587.FStar_Syntax_Syntax.fv_name in
                     uu____13582.FStar_Syntax_Syntax.v in
                   let uu____13591 =
                     let uu____13592 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13592 in
                   if uu____13591
                   then
                     let val_decl =
                       let uu___153_13607 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___153_13607.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___153_13607.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___153_13607.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13611 = encode_sigelt' env1 val_decl in
                     match uu____13611 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____13575 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13628,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13630;
                          FStar_Syntax_Syntax.lbtyp = uu____13631;
                          FStar_Syntax_Syntax.lbeff = uu____13632;
                          FStar_Syntax_Syntax.lbdef = uu____13633;_}::[]),uu____13634,uu____13635)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13649 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13649 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13672 =
                   let uu____13674 =
                     let uu____13675 =
                       let uu____13679 =
                         let uu____13680 =
                           let uu____13686 =
                             let uu____13687 =
                               let uu____13690 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13690) in
                             FStar_SMTEncoding_Util.mkEq uu____13687 in
                           ([[b2t_x]], [xx], uu____13686) in
                         FStar_SMTEncoding_Util.mkForall uu____13680 in
                       (uu____13679, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13675 in
                   [uu____13674] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13672 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13707,uu____13708,uu____13709)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___120_13715  ->
                  match uu___120_13715 with
                  | FStar_Syntax_Syntax.Discriminator uu____13716 -> true
                  | uu____13717 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13719,lids,uu____13721) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13728 =
                     let uu____13729 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13729.FStar_Ident.idText in
                   uu____13728 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___121_13731  ->
                     match uu___121_13731 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13732 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13735,uu____13736)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___122_13746  ->
                  match uu___122_13746 with
                  | FStar_Syntax_Syntax.Projector uu____13747 -> true
                  | uu____13750 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13757 = try_lookup_free_var env l in
          (match uu____13757 with
           | Some uu____13761 -> ([], env)
           | None  ->
               let se1 =
                 let uu___154_13764 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___154_13764.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___154_13764.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13770,uu____13771) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13783) ->
          let uu____13788 = encode_sigelts env ses in
          (match uu____13788 with
           | (g,env1) ->
               let uu____13798 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___123_13808  ->
                         match uu___123_13808 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13809;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13810;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13811;_}
                             -> false
                         | uu____13813 -> true)) in
               (match uu____13798 with
                | (g',inversions) ->
                    let uu____13822 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___124_13832  ->
                              match uu___124_13832 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13833 ->
                                  true
                              | uu____13839 -> false)) in
                    (match uu____13822 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13850,tps,k,uu____13853,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___125_13863  ->
                    match uu___125_13863 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13864 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13871 = c in
              match uu____13871 with
              | (name,args,uu____13875,uu____13876,uu____13877) ->
                  let uu____13880 =
                    let uu____13881 =
                      let uu____13887 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13894  ->
                                match uu____13894 with
                                | (uu____13898,sort,uu____13900) -> sort)) in
                      (name, uu____13887, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13881 in
                  [uu____13880]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13918 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13921 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13921 FStar_Option.isNone)) in
            if uu____13918
            then []
            else
              (let uu____13938 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13938 with
               | (xxsym,xx) ->
                   let uu____13944 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13955  ->
                             fun l  ->
                               match uu____13955 with
                               | (out,decls) ->
                                   let uu____13967 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13967 with
                                    | (uu____13973,data_t) ->
                                        let uu____13975 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13975 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____14004 =
                                                 let uu____14005 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____14005.FStar_Syntax_Syntax.n in
                                               match uu____14004 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____14013,indices) ->
                                                   indices
                                               | uu____14029 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____14041  ->
                                                         match uu____14041
                                                         with
                                                         | (x,uu____14045) ->
                                                             let uu____14046
                                                               =
                                                               let uu____14047
                                                                 =
                                                                 let uu____14051
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____14051,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14047 in
                                                             push_term_var
                                                               env1 x
                                                               uu____14046)
                                                    env) in
                                             let uu____14053 =
                                               encode_args indices env1 in
                                             (match uu____14053 with
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
                                                      let uu____14073 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14081
                                                                 =
                                                                 let uu____14084
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____14084,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14081)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____14073
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____14086 =
                                                      let uu____14087 =
                                                        let uu____14090 =
                                                          let uu____14091 =
                                                            let uu____14094 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____14094,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14091 in
                                                        (out, uu____14090) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14087 in
                                                    (uu____14086,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13944 with
                    | (data_ax,decls) ->
                        let uu____14102 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14102 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14113 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14113 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14116 =
                                 let uu____14120 =
                                   let uu____14121 =
                                     let uu____14127 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14135 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14127,
                                       uu____14135) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14121 in
                                 let uu____14143 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14120, (Some "inversion axiom"),
                                   uu____14143) in
                               FStar_SMTEncoding_Util.mkAssume uu____14116 in
                             let pattern_guarded_inversion =
                               let uu____14147 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14147
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14155 =
                                   let uu____14156 =
                                     let uu____14160 =
                                       let uu____14161 =
                                         let uu____14167 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14175 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14167, uu____14175) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14161 in
                                     let uu____14183 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14160, (Some "inversion axiom"),
                                       uu____14183) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14156 in
                                 [uu____14155]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14186 =
            let uu____14194 =
              let uu____14195 = FStar_Syntax_Subst.compress k in
              uu____14195.FStar_Syntax_Syntax.n in
            match uu____14194 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14224 -> (tps, k) in
          (match uu____14186 with
           | (formals,res) ->
               let uu____14239 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14239 with
                | (formals1,res1) ->
                    let uu____14246 = encode_binders None formals1 env in
                    (match uu____14246 with
                     | (vars,guards,env',binder_decls,uu____14261) ->
                         let uu____14268 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14268 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14281 =
                                  let uu____14285 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14285) in
                                FStar_SMTEncoding_Util.mkApp uu____14281 in
                              let uu____14290 =
                                let tname_decl =
                                  let uu____14296 =
                                    let uu____14297 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14312  ->
                                              match uu____14312 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14320 = varops.next_id () in
                                    (tname, uu____14297,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14320, false) in
                                  constructor_or_logic_type_decl uu____14296 in
                                let uu____14325 =
                                  match vars with
                                  | [] ->
                                      let uu____14332 =
                                        let uu____14333 =
                                          let uu____14335 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14335 in
                                        push_free_var env1 t tname
                                          uu____14333 in
                                      ([], uu____14332)
                                  | uu____14339 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14345 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14345 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14354 =
                                          let uu____14358 =
                                            let uu____14359 =
                                              let uu____14367 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14367) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14359 in
                                          (uu____14358,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14354 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14325 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14290 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14390 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14390 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14404 =
                                               let uu____14405 =
                                                 let uu____14409 =
                                                   let uu____14410 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14410 in
                                                 (uu____14409,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14405 in
                                             [uu____14404]
                                           else [] in
                                         let uu____14413 =
                                           let uu____14415 =
                                             let uu____14417 =
                                               let uu____14418 =
                                                 let uu____14422 =
                                                   let uu____14423 =
                                                     let uu____14429 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14429) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14423 in
                                                 (uu____14422, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14418 in
                                             [uu____14417] in
                                           FStar_List.append karr uu____14415 in
                                         FStar_List.append decls1 uu____14413 in
                                   let aux =
                                     let uu____14438 =
                                       let uu____14440 =
                                         inversion_axioms tapp vars in
                                       let uu____14442 =
                                         let uu____14444 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14444] in
                                       FStar_List.append uu____14440
                                         uu____14442 in
                                     FStar_List.append kindingAx uu____14438 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14449,uu____14450,uu____14451,uu____14452,uu____14453)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14458,t,uu____14460,n_tps,uu____14462) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14467 = new_term_constant_and_tok_from_lid env d in
          (match uu____14467 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14478 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14478 with
                | (formals,t_res) ->
                    let uu____14500 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14500 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14509 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14509 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14547 =
                                            mk_term_projector_name d x in
                                          (uu____14547,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14549 =
                                  let uu____14559 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14559, true) in
                                FStar_All.pipe_right uu____14549
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
                              let uu____14581 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14581 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14589::uu____14590 ->
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
                                         let uu____14615 =
                                           let uu____14621 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14621) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14615
                                     | uu____14634 -> tok_typing in
                                   let uu____14639 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14639 with
                                    | (vars',guards',env'',decls_formals,uu____14654)
                                        ->
                                        let uu____14661 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14661 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14680 ->
                                                   let uu____14684 =
                                                     let uu____14685 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14685 in
                                                   [uu____14684] in
                                             let encode_elim uu____14692 =
                                               let uu____14693 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14693 with
                                               | (head1,args) ->
                                                   let uu____14722 =
                                                     let uu____14723 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14723.FStar_Syntax_Syntax.n in
                                                   (match uu____14722 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____14730;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14731;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14732;_},uu____14733)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14743 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14743
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
                                                                 | uu____14769
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14777
                                                                    =
                                                                    let uu____14778
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14778 in
                                                                    if
                                                                    uu____14777
                                                                    then
                                                                    let uu____14785
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14785]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14787
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14800
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14800
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14822
                                                                    =
                                                                    let uu____14826
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14826 in
                                                                    (match uu____14822
                                                                    with
                                                                    | 
                                                                    (uu____14833,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14839
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14839
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14841
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14841
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
                                                             (match uu____14787
                                                              with
                                                              | (uu____14849,arg_vars,elim_eqns_or_guards,uu____14852)
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
                                                                    let uu____14871
                                                                    =
                                                                    let uu____14875
                                                                    =
                                                                    let uu____14876
                                                                    =
                                                                    let uu____14882
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14888
                                                                    =
                                                                    let uu____14889
                                                                    =
                                                                    let uu____14892
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14892) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14889 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14882,
                                                                    uu____14888) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14876 in
                                                                    (uu____14875,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14871 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14905
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14905,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14907
                                                                    =
                                                                    let uu____14911
                                                                    =
                                                                    let uu____14912
                                                                    =
                                                                    let uu____14918
                                                                    =
                                                                    let uu____14921
                                                                    =
                                                                    let uu____14923
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14923] in
                                                                    [uu____14921] in
                                                                    let uu____14926
                                                                    =
                                                                    let uu____14927
                                                                    =
                                                                    let uu____14930
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14931
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14930,
                                                                    uu____14931) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14927 in
                                                                    (uu____14918,
                                                                    [x],
                                                                    uu____14926) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14912 in
                                                                    let uu____14941
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14911,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14941) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14907
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14946
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
                                                                    (let uu____14961
                                                                    =
                                                                    let uu____14962
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14962
                                                                    dapp1 in
                                                                    [uu____14961]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14946
                                                                    FStar_List.flatten in
                                                                    let uu____14966
                                                                    =
                                                                    let uu____14970
                                                                    =
                                                                    let uu____14971
                                                                    =
                                                                    let uu____14977
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14983
                                                                    =
                                                                    let uu____14984
                                                                    =
                                                                    let uu____14987
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14987) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14984 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14977,
                                                                    uu____14983) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14971 in
                                                                    (uu____14970,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14966) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____15003 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15003
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
                                                                 | uu____15029
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15037
                                                                    =
                                                                    let uu____15038
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15038 in
                                                                    if
                                                                    uu____15037
                                                                    then
                                                                    let uu____15045
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15045]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15047
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15060
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15060
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15082
                                                                    =
                                                                    let uu____15086
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15086 in
                                                                    (match uu____15082
                                                                    with
                                                                    | 
                                                                    (uu____15093,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15099
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15099
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15101
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15101
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
                                                             (match uu____15047
                                                              with
                                                              | (uu____15109,arg_vars,elim_eqns_or_guards,uu____15112)
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
                                                                    let uu____15131
                                                                    =
                                                                    let uu____15135
                                                                    =
                                                                    let uu____15136
                                                                    =
                                                                    let uu____15142
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15148
                                                                    =
                                                                    let uu____15149
                                                                    =
                                                                    let uu____15152
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15152) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15149 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15142,
                                                                    uu____15148) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15136 in
                                                                    (uu____15135,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15131 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15165
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15165,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15167
                                                                    =
                                                                    let uu____15171
                                                                    =
                                                                    let uu____15172
                                                                    =
                                                                    let uu____15178
                                                                    =
                                                                    let uu____15181
                                                                    =
                                                                    let uu____15183
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15183] in
                                                                    [uu____15181] in
                                                                    let uu____15186
                                                                    =
                                                                    let uu____15187
                                                                    =
                                                                    let uu____15190
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15191
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15190,
                                                                    uu____15191) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15187 in
                                                                    (uu____15178,
                                                                    [x],
                                                                    uu____15186) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15172 in
                                                                    let uu____15201
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15171,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15201) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15167
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15206
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
                                                                    (let uu____15221
                                                                    =
                                                                    let uu____15222
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15222
                                                                    dapp1 in
                                                                    [uu____15221]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15206
                                                                    FStar_List.flatten in
                                                                    let uu____15226
                                                                    =
                                                                    let uu____15230
                                                                    =
                                                                    let uu____15231
                                                                    =
                                                                    let uu____15237
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15243
                                                                    =
                                                                    let uu____15244
                                                                    =
                                                                    let uu____15247
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15247) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15244 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15237,
                                                                    uu____15243) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15231 in
                                                                    (uu____15230,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15226) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15257 ->
                                                        ((let uu____15259 =
                                                            let uu____15260 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15261 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15260
                                                              uu____15261 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15259);
                                                         ([], []))) in
                                             let uu____15264 = encode_elim () in
                                             (match uu____15264 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15276 =
                                                      let uu____15278 =
                                                        let uu____15280 =
                                                          let uu____15282 =
                                                            let uu____15284 =
                                                              let uu____15285
                                                                =
                                                                let uu____15291
                                                                  =
                                                                  let uu____15293
                                                                    =
                                                                    let uu____15294
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15294 in
                                                                  Some
                                                                    uu____15293 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15291) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15285 in
                                                            [uu____15284] in
                                                          let uu____15297 =
                                                            let uu____15299 =
                                                              let uu____15301
                                                                =
                                                                let uu____15303
                                                                  =
                                                                  let uu____15305
                                                                    =
                                                                    let uu____15307
                                                                    =
                                                                    let uu____15309
                                                                    =
                                                                    let uu____15310
                                                                    =
                                                                    let uu____15314
                                                                    =
                                                                    let uu____15315
                                                                    =
                                                                    let uu____15321
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15321) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15315 in
                                                                    (uu____15314,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15310 in
                                                                    let uu____15328
                                                                    =
                                                                    let uu____15330
                                                                    =
                                                                    let uu____15331
                                                                    =
                                                                    let uu____15335
                                                                    =
                                                                    let uu____15336
                                                                    =
                                                                    let uu____15342
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____15348
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15342,
                                                                    uu____15348) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15336 in
                                                                    (uu____15335,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15331 in
                                                                    [uu____15330] in
                                                                    uu____15309
                                                                    ::
                                                                    uu____15328 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15307 in
                                                                  FStar_List.append
                                                                    uu____15305
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15303 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15301 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15299 in
                                                          FStar_List.append
                                                            uu____15282
                                                            uu____15297 in
                                                        FStar_List.append
                                                          decls3 uu____15280 in
                                                      FStar_List.append
                                                        decls2 uu____15278 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15276 in
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
           (fun uu____15369  ->
              fun se  ->
                match uu____15369 with
                | (g,env1) ->
                    let uu____15381 = encode_sigelt env1 se in
                    (match uu____15381 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15417 =
        match uu____15417 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15435 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____15440 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15440
                   then
                     let uu____15441 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15442 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15443 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15441 uu____15442 uu____15443
                   else ());
                  (let uu____15445 = encode_term t1 env1 in
                   match uu____15445 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15455 =
                         let uu____15459 =
                           let uu____15460 =
                             let uu____15461 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15461
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15460 in
                         new_term_constant_from_string env1 x uu____15459 in
                       (match uu____15455 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15472 = FStar_Options.log_queries () in
                              if uu____15472
                              then
                                let uu____15474 =
                                  let uu____15475 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15476 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15477 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15475 uu____15476 uu____15477 in
                                Some uu____15474
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15488,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15497 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15497 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15510,se,uu____15512) ->
                 let uu____15515 = encode_sigelt env1 se in
                 (match uu____15515 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15525,se) ->
                 let uu____15529 = encode_sigelt env1 se in
                 (match uu____15529 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15539 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15539 with | (uu____15551,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15596  ->
            match uu____15596 with
            | (l,uu____15603,uu____15604) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15625  ->
            match uu____15625 with
            | (l,uu____15633,uu____15634) ->
                let uu____15639 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39) (
                    fst l) in
                let uu____15640 =
                  let uu____15642 =
                    let uu____15643 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15643 in
                  [uu____15642] in
                uu____15639 :: uu____15640)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15654 =
      let uu____15656 =
        let uu____15657 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15659 =
          let uu____15660 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15660 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15657;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15659
        } in
      [uu____15656] in
    FStar_ST.write last_env uu____15654
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15670 = FStar_ST.read last_env in
      match uu____15670 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15676 ->
          let uu___155_15678 = e in
          let uu____15679 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___155_15678.bindings);
            depth = (uu___155_15678.depth);
            tcenv;
            warn = (uu___155_15678.warn);
            cache = (uu___155_15678.cache);
            nolabels = (uu___155_15678.nolabels);
            use_zfuel_name = (uu___155_15678.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_15678.encode_non_total_function_typ);
            current_module_name = uu____15679
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15683 = FStar_ST.read last_env in
    match uu____15683 with
    | [] -> failwith "Empty env stack"
    | uu____15688::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15696  ->
    let uu____15697 = FStar_ST.read last_env in
    match uu____15697 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___156_15708 = hd1 in
          {
            bindings = (uu___156_15708.bindings);
            depth = (uu___156_15708.depth);
            tcenv = (uu___156_15708.tcenv);
            warn = (uu___156_15708.warn);
            cache = refs;
            nolabels = (uu___156_15708.nolabels);
            use_zfuel_name = (uu___156_15708.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___156_15708.encode_non_total_function_typ);
            current_module_name = (uu___156_15708.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15714  ->
    let uu____15715 = FStar_ST.read last_env in
    match uu____15715 with
    | [] -> failwith "Popping an empty stack"
    | uu____15720::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15728  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15731  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15734  ->
    let uu____15735 = FStar_ST.read last_env in
    match uu____15735 with
    | hd1::uu____15741::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15747 -> failwith "Impossible"
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
        | (uu____15796::uu____15797,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___157_15801 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___157_15801.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___157_15801.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___157_15801.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15802 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15813 =
        let uu____15815 =
          let uu____15816 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15816 in
        let uu____15817 = open_fact_db_tags env in uu____15815 :: uu____15817 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15813
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
      let uu____15832 = encode_sigelt env se in
      match uu____15832 with
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
        let uu____15857 = FStar_Options.log_queries () in
        if uu____15857
        then
          let uu____15859 =
            let uu____15860 =
              let uu____15861 =
                let uu____15862 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15862 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15861 in
            FStar_SMTEncoding_Term.Caption uu____15860 in
          uu____15859 :: decls
        else decls in
      let env =
        let uu____15869 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15869 tcenv in
      let uu____15870 = encode_top_level_facts env se in
      match uu____15870 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15879 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15879))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15890 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15890
       then
         let uu____15891 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15891
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15912  ->
                 fun se  ->
                   match uu____15912 with
                   | (g,env2) ->
                       let uu____15924 = encode_top_level_facts env2 se in
                       (match uu____15924 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15937 =
         encode_signature
           (let uu___158_15941 = env in
            {
              bindings = (uu___158_15941.bindings);
              depth = (uu___158_15941.depth);
              tcenv = (uu___158_15941.tcenv);
              warn = false;
              cache = (uu___158_15941.cache);
              nolabels = (uu___158_15941.nolabels);
              use_zfuel_name = (uu___158_15941.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___158_15941.encode_non_total_function_typ);
              current_module_name = (uu___158_15941.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15937 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15953 = FStar_Options.log_queries () in
             if uu____15953
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___159_15958 = env1 in
               {
                 bindings = (uu___159_15958.bindings);
                 depth = (uu___159_15958.depth);
                 tcenv = (uu___159_15958.tcenv);
                 warn = true;
                 cache = (uu___159_15958.cache);
                 nolabels = (uu___159_15958.nolabels);
                 use_zfuel_name = (uu___159_15958.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___159_15958.encode_non_total_function_typ);
                 current_module_name = (uu___159_15958.current_module_name)
               });
            (let uu____15960 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15960
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
        (let uu____15995 =
           let uu____15996 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15996.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15995);
        (let env =
           let uu____15998 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15998 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____16005 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16026 = aux rest in
                 (match uu____16026 with
                  | (out,rest1) ->
                      let t =
                        let uu____16044 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____16044 with
                        | Some uu____16048 ->
                            let uu____16049 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16049
                              x.FStar_Syntax_Syntax.sort
                        | uu____16050 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____16053 =
                        let uu____16055 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___160_16056 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___160_16056.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___160_16056.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16055 :: out in
                      (uu____16053, rest1))
             | uu____16059 -> ([], bindings1) in
           let uu____16063 = aux bindings in
           match uu____16063 with
           | (closing,bindings1) ->
               let uu____16077 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16077, bindings1) in
         match uu____16005 with
         | (q1,bindings1) ->
             let uu____16090 =
               let uu____16093 =
                 FStar_List.filter
                   (fun uu___126_16095  ->
                      match uu___126_16095 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16096 ->
                          false
                      | uu____16100 -> true) bindings1 in
               encode_env_bindings env uu____16093 in
             (match uu____16090 with
              | (env_decls,env1) ->
                  ((let uu____16111 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16111
                    then
                      let uu____16112 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16112
                    else ());
                   (let uu____16114 = encode_formula q1 env1 in
                    match uu____16114 with
                    | (phi,qdecls) ->
                        let uu____16126 =
                          let uu____16129 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16129 phi in
                        (match uu____16126 with
                         | (labels,phi1) ->
                             let uu____16139 = encode_labels labels in
                             (match uu____16139 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____16160 =
                                      let uu____16164 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16165 =
                                        varops.mk_unique "@query" in
                                      (uu____16164, (Some "query"),
                                        uu____16165) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16160 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16178 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16178 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16180 = encode_formula q env in
       match uu____16180 with
       | (f,uu____16184) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16186) -> true
             | uu____16189 -> false)))