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
             let uu____3524 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3524 in
           let uu____3528 = encode_term_pred None k env ttm in
           (match uu____3528 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3536 =
                    let uu____3540 =
                      let uu____3541 =
                        let uu____3542 =
                          let uu____3543 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3543 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3542 in
                      varops.mk_unique uu____3541 in
                    (t_has_k, (Some "Uvar typing"), uu____3540) in
                  FStar_SMTEncoding_Util.mkAssume uu____3536 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3549 ->
           let uu____3559 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3559 with
            | (head1,args_e) ->
                let uu____3587 =
                  let uu____3595 =
                    let uu____3596 = FStar_Syntax_Subst.compress head1 in
                    uu____3596.FStar_Syntax_Syntax.n in
                  (uu____3595, args_e) in
                (match uu____3587 with
                 | uu____3606 when head_redex env head1 ->
                     let uu____3614 = whnf env t in
                     encode_term uu____3614 env
                 | uu____3615 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____3628;
                       FStar_Syntax_Syntax.pos = uu____3629;
                       FStar_Syntax_Syntax.vars = uu____3630;_},uu____3631),uu____3632::
                    (v1,uu____3634)::(v2,uu____3636)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3674 = encode_term v1 env in
                     (match uu____3674 with
                      | (v11,decls1) ->
                          let uu____3681 = encode_term v2 env in
                          (match uu____3681 with
                           | (v21,decls2) ->
                               let uu____3688 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3688,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3691::(v1,uu____3693)::(v2,uu____3695)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3729 = encode_term v1 env in
                     (match uu____3729 with
                      | (v11,decls1) ->
                          let uu____3736 = encode_term v2 env in
                          (match uu____3736 with
                           | (v21,decls2) ->
                               let uu____3743 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3743,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3745) ->
                     let e0 =
                       let uu____3757 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3757 in
                     ((let uu____3763 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3763
                       then
                         let uu____3764 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3764
                       else ());
                      (let e =
                         let uu____3769 =
                           let uu____3770 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3771 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3770
                             uu____3771 in
                         uu____3769 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3780),(arg,uu____3782)::[]) -> encode_term arg env
                 | uu____3800 ->
                     let uu____3808 = encode_args args_e env in
                     (match uu____3808 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3841 = encode_term head1 env in
                            match uu____3841 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3880 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3880 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3922  ->
                                                 fun uu____3923  ->
                                                   match (uu____3922,
                                                           uu____3923)
                                                   with
                                                   | ((bv,uu____3937),
                                                      (a,uu____3939)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3953 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3953
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3958 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3958 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3968 =
                                                   let uu____3972 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3977 =
                                                     let uu____3978 =
                                                       let uu____3979 =
                                                         let uu____3980 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3980 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3979 in
                                                     varops.mk_unique
                                                       uu____3978 in
                                                   (uu____3972,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3977) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3968 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3997 = lookup_free_var_sym env fv in
                            match uu____3997 with
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
                                   FStar_Syntax_Syntax.tk = uu____4020;
                                   FStar_Syntax_Syntax.pos = uu____4021;
                                   FStar_Syntax_Syntax.vars = uu____4022;_},uu____4023)
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____4034;
                                   FStar_Syntax_Syntax.pos = uu____4035;
                                   FStar_Syntax_Syntax.vars = uu____4036;_},uu____4037)
                                ->
                                let uu____4042 =
                                  let uu____4043 =
                                    let uu____4046 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4046
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4043
                                    FStar_Pervasives.snd in
                                Some uu____4042
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4066 =
                                  let uu____4067 =
                                    let uu____4070 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4070
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4067
                                    FStar_Pervasives.snd in
                                Some uu____4066
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4089,(FStar_Util.Inl t1,uu____4091),uu____4092)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4130,(FStar_Util.Inr c,uu____4132),uu____4133)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4171 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4191 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4191 in
                               let uu____4192 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4192 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4202;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4203;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4204;_},uu____4205)
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
                                     | uu____4229 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4274 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4274 with
            | (bs1,body1,opening) ->
                let fallback uu____4289 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____4294 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4294, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4305 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____4305
                  | FStar_Util.Inr (eff,uu____4307) ->
                      let uu____4313 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____4313 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4358 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___137_4359 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___137_4359.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___137_4359.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___137_4359.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___137_4359.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___137_4359.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___137_4359.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___137_4359.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___137_4359.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___137_4359.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___137_4359.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___137_4359.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___137_4359.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___137_4359.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___137_4359.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___137_4359.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___137_4359.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___137_4359.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___137_4359.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___137_4359.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___137_4359.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___137_4359.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___137_4359.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___137_4359.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___137_4359.FStar_TypeChecker_Env.proof_ns)
                             }) uu____4358 FStar_Syntax_Syntax.U_unknown in
                        let uu____4360 =
                          let uu____4361 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4361 in
                        FStar_Util.Inl uu____4360
                    | FStar_Util.Inr (eff_name,uu____4368) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4399 =
                        let uu____4400 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4400 in
                      FStar_All.pipe_right uu____4399
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4412 =
                        let uu____4413 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4413 FStar_Pervasives.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4421 =
                          let uu____4422 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4422 in
                        FStar_All.pipe_right uu____4421
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4426 =
                             let uu____4427 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4427 in
                           FStar_All.pipe_right uu____4426
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4438 =
                         let uu____4439 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4439 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4438);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4454 =
                       (is_impure lc1) &&
                         (let uu____4455 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4455) in
                     if uu____4454
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4460 = encode_binders None bs1 env in
                        match uu____4460 with
                        | (vars,guards,envbody,decls,uu____4475) ->
                            let uu____4482 =
                              let uu____4490 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4490
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4482 with
                             | (lc2,body2) ->
                                 let uu____4515 = encode_term body2 envbody in
                                 (match uu____4515 with
                                  | (body3,decls') ->
                                      let uu____4522 =
                                        let uu____4527 = codomain_eff lc2 in
                                        match uu____4527 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4539 =
                                              encode_term tfun env in
                                            (match uu____4539 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4522 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4558 =
                                               let uu____4564 =
                                                 let uu____4565 =
                                                   let uu____4568 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4568, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4565 in
                                               ([], vars, uu____4564) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4558 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4576 =
                                                   let uu____4578 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4578 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4576 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4589 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4589 with
                                            | Some cache_entry ->
                                                let uu____4594 =
                                                  let uu____4595 =
                                                    let uu____4599 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4599) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4595 in
                                                (uu____4594,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | None  ->
                                                let uu____4605 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4605 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4612 =
                                                         let uu____4613 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4613 =
                                                           cache_size in
                                                       if uu____4612
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
                                                         let uu____4624 =
                                                           let uu____4625 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4625 in
                                                         varops.mk_unique
                                                           uu____4624 in
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
                                                       let uu____4630 =
                                                         let uu____4634 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4634) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4630 in
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
                                                           let uu____4646 =
                                                             let uu____4647 =
                                                               let uu____4651
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4651,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4647 in
                                                           [uu____4646] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4659 =
                                                         let uu____4663 =
                                                           let uu____4664 =
                                                             let uu____4670 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4670) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4664 in
                                                         (uu____4663,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4659 in
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
                                                     ((let uu____4680 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4680);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4682,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4683;
                          FStar_Syntax_Syntax.lbunivs = uu____4684;
                          FStar_Syntax_Syntax.lbtyp = uu____4685;
                          FStar_Syntax_Syntax.lbeff = uu____4686;
                          FStar_Syntax_Syntax.lbdef = uu____4687;_}::uu____4688),uu____4689)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4707;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4709;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4725 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4738 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4738, [decl_e])))
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
              let uu____4780 = encode_term e1 env in
              match uu____4780 with
              | (ee1,decls1) ->
                  let uu____4787 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4787 with
                   | (xs,e21) ->
                       let uu____4801 = FStar_List.hd xs in
                       (match uu____4801 with
                        | (x1,uu____4809) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4811 = encode_body e21 env' in
                            (match uu____4811 with
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
            let uu____4833 =
              let uu____4837 =
                let uu____4838 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4838 in
              gen_term_var env uu____4837 in
            match uu____4833 with
            | (scrsym,scr',env1) ->
                let uu____4848 = encode_term e env1 in
                (match uu____4848 with
                 | (scr,decls) ->
                     let uu____4855 =
                       let encode_branch b uu____4871 =
                         match uu____4871 with
                         | (else_case,decls1) ->
                             let uu____4882 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4882 with
                              | (p,w,br) ->
                                  let uu____4903 = encode_pat env1 p in
                                  (match uu____4903 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____4923  ->
                                                   match uu____4923 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____4928 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____4943 =
                                               encode_term w1 env2 in
                                             (match uu____4943 with
                                              | (w2,decls2) ->
                                                  let uu____4951 =
                                                    let uu____4952 =
                                                      let uu____4955 =
                                                        let uu____4956 =
                                                          let uu____4959 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____4959) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____4956 in
                                                      (guard, uu____4955) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____4952 in
                                                  (uu____4951, decls2)) in
                                       (match uu____4928 with
                                        | (guard1,decls2) ->
                                            let uu____4967 =
                                              encode_br br env2 in
                                            (match uu____4967 with
                                             | (br1,decls3) ->
                                                 let uu____4975 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____4975,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4855 with
                      | (match_tm,decls1) ->
                          let uu____4986 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4986, decls1)))
and encode_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____5008 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5008
       then
         let uu____5009 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5009
       else ());
      (let uu____5011 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5011 with
       | (vars,pat_term) ->
           let uu____5021 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5044  ->
                     fun v1  ->
                       match uu____5044 with
                       | (env1,vars1) ->
                           let uu____5072 = gen_term_var env1 v1 in
                           (match uu____5072 with
                            | (xx,uu____5084,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____5021 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5131 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5132 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5133 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5139 =
                        let uu____5142 = encode_const c in
                        (scrutinee, uu____5142) in
                      FStar_SMTEncoding_Util.mkEq uu____5139
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5161 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5161 with
                        | (uu____5165,uu____5166::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5168 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5189  ->
                                  match uu____5189 with
                                  | (arg,uu____5195) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5205 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5205)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5225) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5244 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5259 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5281  ->
                                  match uu____5281 with
                                  | (arg,uu____5290) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5300 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5300)) in
                      FStar_All.pipe_right uu____5259 FStar_List.flatten in
                let pat_term1 uu____5316 = encode_term pat_term env1 in
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
      let uu____5323 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5338  ->
                fun uu____5339  ->
                  match (uu____5338, uu____5339) with
                  | ((tms,decls),(t,uu____5359)) ->
                      let uu____5370 = encode_term t env in
                      (match uu____5370 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5323 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5404 = FStar_Syntax_Util.list_elements e in
        match uu____5404 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5422 =
          let uu____5432 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5432 FStar_Syntax_Util.head_and_args in
        match uu____5422 with
        | (head1,args) ->
            let uu____5463 =
              let uu____5471 =
                let uu____5472 = FStar_Syntax_Util.un_uinst head1 in
                uu____5472.FStar_Syntax_Syntax.n in
              (uu____5471, args) in
            (match uu____5463 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5486,uu____5487)::(e,uu____5489)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> (e, None)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5520)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpatT_lid
                 -> (e, None)
             | uu____5541 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or t1 =
          let uu____5574 =
            let uu____5584 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5584 FStar_Syntax_Util.head_and_args in
          match uu____5574 with
          | (head1,args) ->
              let uu____5613 =
                let uu____5621 =
                  let uu____5622 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5622.FStar_Syntax_Syntax.n in
                (uu____5621, args) in
              (match uu____5613 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5635)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5655 -> None) in
        match elts with
        | t1::[] ->
            let uu____5673 = smt_pat_or t1 in
            (match uu____5673 with
             | Some e ->
                 let uu____5689 = list_elements1 e in
                 FStar_All.pipe_right uu____5689
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5706 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5706
                           (FStar_List.map one_pat)))
             | uu____5720 ->
                 let uu____5724 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5724])
        | uu____5755 ->
            let uu____5757 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5757] in
      let uu____5788 =
        let uu____5804 =
          let uu____5805 = FStar_Syntax_Subst.compress t in
          uu____5805.FStar_Syntax_Syntax.n in
        match uu____5804 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5835 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5835 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5870;
                        FStar_Syntax_Syntax.effect_name = uu____5871;
                        FStar_Syntax_Syntax.result_typ = uu____5872;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5874)::(post,uu____5876)::(pats,uu____5878)::[];
                        FStar_Syntax_Syntax.flags = uu____5879;_}
                      ->
                      let uu____5911 = lemma_pats pats in
                      (binders1, pre, post, uu____5911)
                  | uu____5930 -> failwith "impos"))
        | uu____5946 -> failwith "Impos" in
      match uu____5788 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___138_5991 = env in
            {
              bindings = (uu___138_5991.bindings);
              depth = (uu___138_5991.depth);
              tcenv = (uu___138_5991.tcenv);
              warn = (uu___138_5991.warn);
              cache = (uu___138_5991.cache);
              nolabels = (uu___138_5991.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___138_5991.encode_non_total_function_typ);
              current_module_name = (uu___138_5991.current_module_name)
            } in
          let uu____5992 = encode_binders None binders env1 in
          (match uu____5992 with
           | (vars,guards,env2,decls,uu____6007) ->
               let uu____6014 =
                 let uu____6021 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____6052 =
                             let uu____6057 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun uu____6073  ->
                                       match uu____6073 with
                                       | (t1,uu____6080) ->
                                           encode_term t1 env2)) in
                             FStar_All.pipe_right uu____6057 FStar_List.unzip in
                           match uu____6052 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____6021 FStar_List.unzip in
               (match uu____6014 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___139_6130 = env2 in
                      {
                        bindings = (uu___139_6130.bindings);
                        depth = (uu___139_6130.depth);
                        tcenv = (uu___139_6130.tcenv);
                        warn = (uu___139_6130.warn);
                        cache = (uu___139_6130.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___139_6130.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___139_6130.encode_non_total_function_typ);
                        current_module_name =
                          (uu___139_6130.current_module_name)
                      } in
                    let uu____6131 =
                      let uu____6134 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6134 env3 in
                    (match uu____6131 with
                     | (pre1,decls'') ->
                         let uu____6139 =
                           let uu____6142 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6142 env3 in
                         (match uu____6139 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6149 =
                                let uu____6150 =
                                  let uu____6156 =
                                    let uu____6157 =
                                      let uu____6160 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6160, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6157 in
                                  (pats, vars, uu____6156) in
                                FStar_SMTEncoding_Util.mkForall uu____6150 in
                              (uu____6149, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6173 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6173
        then
          let uu____6174 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6175 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6174 uu____6175
        else () in
      let enc f r l =
        let uu____6202 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6215 = encode_term (fst x) env in
                 match uu____6215 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6202 with
        | (decls,args) ->
            let uu____6232 =
              let uu___140_6233 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_6233.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_6233.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6232, decls) in
      let const_op f r uu____6252 = let uu____6255 = f r in (uu____6255, []) in
      let un_op f l =
        let uu____6271 = FStar_List.hd l in FStar_All.pipe_left f uu____6271 in
      let bin_op f uu___112_6284 =
        match uu___112_6284 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6292 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6319 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6328  ->
                 match uu____6328 with
                 | (t,uu____6336) ->
                     let uu____6337 = encode_formula t env in
                     (match uu____6337 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6319 with
        | (decls,phis) ->
            let uu____6354 =
              let uu___141_6355 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___141_6355.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___141_6355.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6354, decls) in
      let eq_op r uu___113_6371 =
        match uu___113_6371 with
        | uu____6374::e1::e2::[] ->
            let uu____6405 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6405 r [e1; e2]
        | uu____6424::uu____6425::e1::e2::[] ->
            let uu____6464 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6464 r [e1; e2]
        | l ->
            let uu____6484 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6484 r l in
      let mk_imp1 r uu___114_6503 =
        match uu___114_6503 with
        | (lhs,uu____6507)::(rhs,uu____6509)::[] ->
            let uu____6530 = encode_formula rhs env in
            (match uu____6530 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6539) ->
                      (l1, decls1)
                  | uu____6542 ->
                      let uu____6543 = encode_formula lhs env in
                      (match uu____6543 with
                       | (l2,decls2) ->
                           let uu____6550 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6550, (FStar_List.append decls1 decls2)))))
        | uu____6552 -> failwith "impossible" in
      let mk_ite r uu___115_6567 =
        match uu___115_6567 with
        | (guard,uu____6571)::(_then,uu____6573)::(_else,uu____6575)::[] ->
            let uu____6604 = encode_formula guard env in
            (match uu____6604 with
             | (g,decls1) ->
                 let uu____6611 = encode_formula _then env in
                 (match uu____6611 with
                  | (t,decls2) ->
                      let uu____6618 = encode_formula _else env in
                      (match uu____6618 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6627 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6646 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6646 in
      let connectives =
        let uu____6658 =
          let uu____6667 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6667) in
        let uu____6680 =
          let uu____6690 =
            let uu____6699 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6699) in
          let uu____6712 =
            let uu____6722 =
              let uu____6732 =
                let uu____6741 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6741) in
              let uu____6754 =
                let uu____6764 =
                  let uu____6774 =
                    let uu____6783 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6783) in
                  [uu____6774;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6764 in
              uu____6732 :: uu____6754 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6722 in
          uu____6690 :: uu____6712 in
        uu____6658 :: uu____6680 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6945 = encode_formula phi' env in
            (match uu____6945 with
             | (phi2,decls) ->
                 let uu____6952 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6952, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6953 ->
            let uu____6958 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6958 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6987 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6987 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6995;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6997;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____7013 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____7013 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____7045::(x,uu____7047)::(t,uu____7049)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____7083 = encode_term x env in
                 (match uu____7083 with
                  | (x1,decls) ->
                      let uu____7090 = encode_term t env in
                      (match uu____7090 with
                       | (t1,decls') ->
                           let uu____7097 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____7097, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____7101)::(msg,uu____7103)::(phi2,uu____7105)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____7139 =
                   let uu____7142 =
                     let uu____7143 = FStar_Syntax_Subst.compress r in
                     uu____7143.FStar_Syntax_Syntax.n in
                   let uu____7146 =
                     let uu____7147 = FStar_Syntax_Subst.compress msg in
                     uu____7147.FStar_Syntax_Syntax.n in
                   (uu____7142, uu____7146) in
                 (match uu____7139 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7154))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____7170 -> fallback phi2)
             | uu____7173 when head_redex env head2 ->
                 let uu____7181 = whnf env phi1 in
                 encode_formula uu____7181 env
             | uu____7182 ->
                 let uu____7190 = encode_term phi1 env in
                 (match uu____7190 with
                  | (tt,decls) ->
                      let uu____7197 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___142_7198 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___142_7198.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___142_7198.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7197, decls)))
        | uu____7201 ->
            let uu____7202 = encode_term phi1 env in
            (match uu____7202 with
             | (tt,decls) ->
                 let uu____7209 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___143_7210 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___143_7210.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___143_7210.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7209, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7237 = encode_binders None bs env1 in
        match uu____7237 with
        | (vars,guards,env2,decls,uu____7259) ->
            let uu____7266 =
              let uu____7273 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7296 =
                          let uu____7301 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7315  ->
                                    match uu____7315 with
                                    | (t,uu____7321) ->
                                        encode_term t
                                          (let uu___144_7322 = env2 in
                                           {
                                             bindings =
                                               (uu___144_7322.bindings);
                                             depth = (uu___144_7322.depth);
                                             tcenv = (uu___144_7322.tcenv);
                                             warn = (uu___144_7322.warn);
                                             cache = (uu___144_7322.cache);
                                             nolabels =
                                               (uu___144_7322.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___144_7322.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___144_7322.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7301 FStar_List.unzip in
                        match uu____7296 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7273 FStar_List.unzip in
            (match uu____7266 with
             | (pats,decls') ->
                 let uu____7374 = encode_formula body env2 in
                 (match uu____7374 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7393;
                             FStar_SMTEncoding_Term.rng = uu____7394;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7402 -> guards in
                      let uu____7405 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7405, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7439  ->
                   match uu____7439 with
                   | (x,uu____7443) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7449 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7455 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7455) uu____7449 tl1 in
             let uu____7457 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7469  ->
                       match uu____7469 with
                       | (b,uu____7473) ->
                           let uu____7474 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7474)) in
             (match uu____7457 with
              | None  -> ()
              | Some (x,uu____7478) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7488 =
                    let uu____7489 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7489 in
                  FStar_Errors.warn pos uu____7488) in
       let uu____7490 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7490 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7496 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7532  ->
                     match uu____7532 with
                     | (l,uu____7542) -> FStar_Ident.lid_equals op l)) in
           (match uu____7496 with
            | None  -> fallback phi1
            | Some (uu____7565,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7594 = encode_q_body env vars pats body in
             match uu____7594 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7620 =
                     let uu____7626 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7626) in
                   FStar_SMTEncoding_Term.mkForall uu____7620
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7638 = encode_q_body env vars pats body in
             match uu____7638 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7663 =
                   let uu____7664 =
                     let uu____7670 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7670) in
                   FStar_SMTEncoding_Term.mkExists uu____7664
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7663, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7719 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7719 with
  | (asym,a) ->
      let uu____7724 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7724 with
       | (xsym,x) ->
           let uu____7729 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7729 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7759 =
                      let uu____7765 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____7765, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7759 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7780 =
                      let uu____7784 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7784) in
                    FStar_SMTEncoding_Util.mkApp uu____7780 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7792 =
                    let uu____7794 =
                      let uu____7796 =
                        let uu____7798 =
                          let uu____7799 =
                            let uu____7803 =
                              let uu____7804 =
                                let uu____7810 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7810) in
                              FStar_SMTEncoding_Util.mkForall uu____7804 in
                            (uu____7803, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7799 in
                        let uu____7819 =
                          let uu____7821 =
                            let uu____7822 =
                              let uu____7826 =
                                let uu____7827 =
                                  let uu____7833 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7833) in
                                FStar_SMTEncoding_Util.mkForall uu____7827 in
                              (uu____7826,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7822 in
                          [uu____7821] in
                        uu____7798 :: uu____7819 in
                      xtok_decl :: uu____7796 in
                    xname_decl :: uu____7794 in
                  (xtok1, uu____7792) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7882 =
                    let uu____7890 =
                      let uu____7896 =
                        let uu____7897 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7897 in
                      quant axy uu____7896 in
                    (FStar_Syntax_Const.op_Eq, uu____7890) in
                  let uu____7903 =
                    let uu____7912 =
                      let uu____7920 =
                        let uu____7926 =
                          let uu____7927 =
                            let uu____7928 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7928 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7927 in
                        quant axy uu____7926 in
                      (FStar_Syntax_Const.op_notEq, uu____7920) in
                    let uu____7934 =
                      let uu____7943 =
                        let uu____7951 =
                          let uu____7957 =
                            let uu____7958 =
                              let uu____7959 =
                                let uu____7962 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7963 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7962, uu____7963) in
                              FStar_SMTEncoding_Util.mkLT uu____7959 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7958 in
                          quant xy uu____7957 in
                        (FStar_Syntax_Const.op_LT, uu____7951) in
                      let uu____7969 =
                        let uu____7978 =
                          let uu____7986 =
                            let uu____7992 =
                              let uu____7993 =
                                let uu____7994 =
                                  let uu____7997 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7998 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7997, uu____7998) in
                                FStar_SMTEncoding_Util.mkLTE uu____7994 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7993 in
                            quant xy uu____7992 in
                          (FStar_Syntax_Const.op_LTE, uu____7986) in
                        let uu____8004 =
                          let uu____8013 =
                            let uu____8021 =
                              let uu____8027 =
                                let uu____8028 =
                                  let uu____8029 =
                                    let uu____8032 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____8033 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____8032, uu____8033) in
                                  FStar_SMTEncoding_Util.mkGT uu____8029 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____8028 in
                              quant xy uu____8027 in
                            (FStar_Syntax_Const.op_GT, uu____8021) in
                          let uu____8039 =
                            let uu____8048 =
                              let uu____8056 =
                                let uu____8062 =
                                  let uu____8063 =
                                    let uu____8064 =
                                      let uu____8067 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____8068 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____8067, uu____8068) in
                                    FStar_SMTEncoding_Util.mkGTE uu____8064 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____8063 in
                                quant xy uu____8062 in
                              (FStar_Syntax_Const.op_GTE, uu____8056) in
                            let uu____8074 =
                              let uu____8083 =
                                let uu____8091 =
                                  let uu____8097 =
                                    let uu____8098 =
                                      let uu____8099 =
                                        let uu____8102 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____8103 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____8102, uu____8103) in
                                      FStar_SMTEncoding_Util.mkSub uu____8099 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8098 in
                                  quant xy uu____8097 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____8091) in
                              let uu____8109 =
                                let uu____8118 =
                                  let uu____8126 =
                                    let uu____8132 =
                                      let uu____8133 =
                                        let uu____8134 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8134 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8133 in
                                    quant qx uu____8132 in
                                  (FStar_Syntax_Const.op_Minus, uu____8126) in
                                let uu____8140 =
                                  let uu____8149 =
                                    let uu____8157 =
                                      let uu____8163 =
                                        let uu____8164 =
                                          let uu____8165 =
                                            let uu____8168 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8169 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8168, uu____8169) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8165 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8164 in
                                      quant xy uu____8163 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8157) in
                                  let uu____8175 =
                                    let uu____8184 =
                                      let uu____8192 =
                                        let uu____8198 =
                                          let uu____8199 =
                                            let uu____8200 =
                                              let uu____8203 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8204 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8203, uu____8204) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8200 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8199 in
                                        quant xy uu____8198 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8192) in
                                    let uu____8210 =
                                      let uu____8219 =
                                        let uu____8227 =
                                          let uu____8233 =
                                            let uu____8234 =
                                              let uu____8235 =
                                                let uu____8238 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8239 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8238, uu____8239) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8235 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8234 in
                                          quant xy uu____8233 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8227) in
                                      let uu____8245 =
                                        let uu____8254 =
                                          let uu____8262 =
                                            let uu____8268 =
                                              let uu____8269 =
                                                let uu____8270 =
                                                  let uu____8273 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8274 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8273, uu____8274) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8270 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8269 in
                                            quant xy uu____8268 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8262) in
                                        let uu____8280 =
                                          let uu____8289 =
                                            let uu____8297 =
                                              let uu____8303 =
                                                let uu____8304 =
                                                  let uu____8305 =
                                                    let uu____8308 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8309 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8308, uu____8309) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8305 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8304 in
                                              quant xy uu____8303 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8297) in
                                          let uu____8315 =
                                            let uu____8324 =
                                              let uu____8332 =
                                                let uu____8338 =
                                                  let uu____8339 =
                                                    let uu____8340 =
                                                      let uu____8343 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8344 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8343,
                                                        uu____8344) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8340 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8339 in
                                                quant xy uu____8338 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8332) in
                                            let uu____8350 =
                                              let uu____8359 =
                                                let uu____8367 =
                                                  let uu____8373 =
                                                    let uu____8374 =
                                                      let uu____8375 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8375 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8374 in
                                                  quant qx uu____8373 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8367) in
                                              [uu____8359] in
                                            uu____8324 :: uu____8350 in
                                          uu____8289 :: uu____8315 in
                                        uu____8254 :: uu____8280 in
                                      uu____8219 :: uu____8245 in
                                    uu____8184 :: uu____8210 in
                                  uu____8149 :: uu____8175 in
                                uu____8118 :: uu____8140 in
                              uu____8083 :: uu____8109 in
                            uu____8048 :: uu____8074 in
                          uu____8013 :: uu____8039 in
                        uu____7978 :: uu____8004 in
                      uu____7943 :: uu____7969 in
                    uu____7912 :: uu____7934 in
                  uu____7882 :: uu____7903 in
                let mk1 l v1 =
                  let uu____8503 =
                    let uu____8508 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8540  ->
                              match uu____8540 with
                              | (l',uu____8549) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8508
                      (FStar_Option.map
                         (fun uu____8582  ->
                            match uu____8582 with | (uu____8593,b) -> b v1)) in
                  FStar_All.pipe_right uu____8503 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8634  ->
                          match uu____8634 with
                          | (l',uu____8643) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8669 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8669 with
        | (xxsym,xx) ->
            let uu____8674 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8674 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8682 =
                   let uu____8686 =
                     let uu____8687 =
                       let uu____8693 =
                         let uu____8694 =
                           let uu____8697 =
                             let uu____8698 =
                               let uu____8701 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8701) in
                             FStar_SMTEncoding_Util.mkEq uu____8698 in
                           (xx_has_type, uu____8697) in
                         FStar_SMTEncoding_Util.mkImp uu____8694 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8693) in
                     FStar_SMTEncoding_Util.mkForall uu____8687 in
                   let uu____8714 =
                     let uu____8715 =
                       let uu____8716 =
                         let uu____8717 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8717 in
                       Prims.strcat module_name uu____8716 in
                     varops.mk_unique uu____8715 in
                   (uu____8686, (Some "pretyping"), uu____8714) in
                 FStar_SMTEncoding_Util.mkAssume uu____8682)
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
    let uu____8747 =
      let uu____8748 =
        let uu____8752 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8752, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8748 in
    let uu____8754 =
      let uu____8756 =
        let uu____8757 =
          let uu____8761 =
            let uu____8762 =
              let uu____8768 =
                let uu____8769 =
                  let uu____8772 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8772) in
                FStar_SMTEncoding_Util.mkImp uu____8769 in
              ([[typing_pred]], [xx], uu____8768) in
            mkForall_fuel uu____8762 in
          (uu____8761, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8757 in
      [uu____8756] in
    uu____8747 :: uu____8754 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8800 =
      let uu____8801 =
        let uu____8805 =
          let uu____8806 =
            let uu____8812 =
              let uu____8815 =
                let uu____8817 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8817] in
              [uu____8815] in
            let uu____8820 =
              let uu____8821 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8821 tt in
            (uu____8812, [bb], uu____8820) in
          FStar_SMTEncoding_Util.mkForall uu____8806 in
        (uu____8805, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8801 in
    let uu____8832 =
      let uu____8834 =
        let uu____8835 =
          let uu____8839 =
            let uu____8840 =
              let uu____8846 =
                let uu____8847 =
                  let uu____8850 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8850) in
                FStar_SMTEncoding_Util.mkImp uu____8847 in
              ([[typing_pred]], [xx], uu____8846) in
            mkForall_fuel uu____8840 in
          (uu____8839, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8835 in
      [uu____8834] in
    uu____8800 :: uu____8832 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8884 =
        let uu____8885 =
          let uu____8889 =
            let uu____8891 =
              let uu____8893 =
                let uu____8895 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8896 =
                  let uu____8898 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8898] in
                uu____8895 :: uu____8896 in
              tt :: uu____8893 in
            tt :: uu____8891 in
          ("Prims.Precedes", uu____8889) in
        FStar_SMTEncoding_Util.mkApp uu____8885 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8884 in
    let precedes_y_x =
      let uu____8901 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8901 in
    let uu____8903 =
      let uu____8904 =
        let uu____8908 =
          let uu____8909 =
            let uu____8915 =
              let uu____8918 =
                let uu____8920 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8920] in
              [uu____8918] in
            let uu____8923 =
              let uu____8924 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8924 tt in
            (uu____8915, [bb], uu____8923) in
          FStar_SMTEncoding_Util.mkForall uu____8909 in
        (uu____8908, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8904 in
    let uu____8935 =
      let uu____8937 =
        let uu____8938 =
          let uu____8942 =
            let uu____8943 =
              let uu____8949 =
                let uu____8950 =
                  let uu____8953 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8953) in
                FStar_SMTEncoding_Util.mkImp uu____8950 in
              ([[typing_pred]], [xx], uu____8949) in
            mkForall_fuel uu____8943 in
          (uu____8942, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8938 in
      let uu____8966 =
        let uu____8968 =
          let uu____8969 =
            let uu____8973 =
              let uu____8974 =
                let uu____8980 =
                  let uu____8981 =
                    let uu____8984 =
                      let uu____8985 =
                        let uu____8987 =
                          let uu____8989 =
                            let uu____8991 =
                              let uu____8992 =
                                let uu____8995 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8996 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8995, uu____8996) in
                              FStar_SMTEncoding_Util.mkGT uu____8992 in
                            let uu____8997 =
                              let uu____8999 =
                                let uu____9000 =
                                  let uu____9003 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____9004 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____9003, uu____9004) in
                                FStar_SMTEncoding_Util.mkGTE uu____9000 in
                              let uu____9005 =
                                let uu____9007 =
                                  let uu____9008 =
                                    let uu____9011 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____9012 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____9011, uu____9012) in
                                  FStar_SMTEncoding_Util.mkLT uu____9008 in
                                [uu____9007] in
                              uu____8999 :: uu____9005 in
                            uu____8991 :: uu____8997 in
                          typing_pred_y :: uu____8989 in
                        typing_pred :: uu____8987 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8985 in
                    (uu____8984, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8981 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8980) in
              mkForall_fuel uu____8974 in
            (uu____8973, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8969 in
        [uu____8968] in
      uu____8937 :: uu____8966 in
    uu____8903 :: uu____8935 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9042 =
      let uu____9043 =
        let uu____9047 =
          let uu____9048 =
            let uu____9054 =
              let uu____9057 =
                let uu____9059 = FStar_SMTEncoding_Term.boxString b in
                [uu____9059] in
              [uu____9057] in
            let uu____9062 =
              let uu____9063 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____9063 tt in
            (uu____9054, [bb], uu____9062) in
          FStar_SMTEncoding_Util.mkForall uu____9048 in
        (uu____9047, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9043 in
    let uu____9074 =
      let uu____9076 =
        let uu____9077 =
          let uu____9081 =
            let uu____9082 =
              let uu____9088 =
                let uu____9089 =
                  let uu____9092 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____9092) in
                FStar_SMTEncoding_Util.mkImp uu____9089 in
              ([[typing_pred]], [xx], uu____9088) in
            mkForall_fuel uu____9082 in
          (uu____9081, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9077 in
      [uu____9076] in
    uu____9042 :: uu____9074 in
  let mk_ref1 env reft_name uu____9114 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____9125 =
        let uu____9129 =
          let uu____9131 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9131] in
        (reft_name, uu____9129) in
      FStar_SMTEncoding_Util.mkApp uu____9125 in
    let refb =
      let uu____9134 =
        let uu____9138 =
          let uu____9140 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9140] in
        (reft_name, uu____9138) in
      FStar_SMTEncoding_Util.mkApp uu____9134 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9144 =
      let uu____9145 =
        let uu____9149 =
          let uu____9150 =
            let uu____9156 =
              let uu____9157 =
                let uu____9160 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9160) in
              FStar_SMTEncoding_Util.mkImp uu____9157 in
            ([[typing_pred]], [xx; aa], uu____9156) in
          mkForall_fuel uu____9150 in
        (uu____9149, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9145 in
    [uu____9144] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9200 =
      let uu____9201 =
        let uu____9205 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9205, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9201 in
    [uu____9200] in
  let mk_and_interp env conj uu____9216 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9233 =
      let uu____9234 =
        let uu____9238 =
          let uu____9239 =
            let uu____9245 =
              let uu____9246 =
                let uu____9249 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9249, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9246 in
            ([[l_and_a_b]], [aa; bb], uu____9245) in
          FStar_SMTEncoding_Util.mkForall uu____9239 in
        (uu____9238, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9234 in
    [uu____9233] in
  let mk_or_interp env disj uu____9273 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9290 =
      let uu____9291 =
        let uu____9295 =
          let uu____9296 =
            let uu____9302 =
              let uu____9303 =
                let uu____9306 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9306, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9303 in
            ([[l_or_a_b]], [aa; bb], uu____9302) in
          FStar_SMTEncoding_Util.mkForall uu____9296 in
        (uu____9295, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9291 in
    [uu____9290] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9347 =
      let uu____9348 =
        let uu____9352 =
          let uu____9353 =
            let uu____9359 =
              let uu____9360 =
                let uu____9363 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9363, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9360 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9359) in
          FStar_SMTEncoding_Util.mkForall uu____9353 in
        (uu____9352, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9348 in
    [uu____9347] in
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
    let uu____9410 =
      let uu____9411 =
        let uu____9415 =
          let uu____9416 =
            let uu____9422 =
              let uu____9423 =
                let uu____9426 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9426, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9423 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9422) in
          FStar_SMTEncoding_Util.mkForall uu____9416 in
        (uu____9415, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9411 in
    [uu____9410] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9471 =
      let uu____9472 =
        let uu____9476 =
          let uu____9477 =
            let uu____9483 =
              let uu____9484 =
                let uu____9487 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9487, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9484 in
            ([[l_imp_a_b]], [aa; bb], uu____9483) in
          FStar_SMTEncoding_Util.mkForall uu____9477 in
        (uu____9476, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9472 in
    [uu____9471] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9528 =
      let uu____9529 =
        let uu____9533 =
          let uu____9534 =
            let uu____9540 =
              let uu____9541 =
                let uu____9544 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9544, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9541 in
            ([[l_iff_a_b]], [aa; bb], uu____9540) in
          FStar_SMTEncoding_Util.mkForall uu____9534 in
        (uu____9533, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9529 in
    [uu____9528] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9578 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9578 in
    let uu____9580 =
      let uu____9581 =
        let uu____9585 =
          let uu____9586 =
            let uu____9592 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9592) in
          FStar_SMTEncoding_Util.mkForall uu____9586 in
        (uu____9585, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9581 in
    [uu____9580] in
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
      let uu____9632 =
        let uu____9636 =
          let uu____9638 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9638] in
        ("Valid", uu____9636) in
      FStar_SMTEncoding_Util.mkApp uu____9632 in
    let uu____9640 =
      let uu____9641 =
        let uu____9645 =
          let uu____9646 =
            let uu____9652 =
              let uu____9653 =
                let uu____9656 =
                  let uu____9657 =
                    let uu____9663 =
                      let uu____9666 =
                        let uu____9668 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9668] in
                      [uu____9666] in
                    let uu____9671 =
                      let uu____9672 =
                        let uu____9675 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9675, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9672 in
                    (uu____9663, [xx1], uu____9671) in
                  FStar_SMTEncoding_Util.mkForall uu____9657 in
                (uu____9656, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9653 in
            ([[l_forall_a_b]], [aa; bb], uu____9652) in
          FStar_SMTEncoding_Util.mkForall uu____9646 in
        (uu____9645, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9641 in
    [uu____9640] in
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
      let uu____9726 =
        let uu____9730 =
          let uu____9732 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9732] in
        ("Valid", uu____9730) in
      FStar_SMTEncoding_Util.mkApp uu____9726 in
    let uu____9734 =
      let uu____9735 =
        let uu____9739 =
          let uu____9740 =
            let uu____9746 =
              let uu____9747 =
                let uu____9750 =
                  let uu____9751 =
                    let uu____9757 =
                      let uu____9760 =
                        let uu____9762 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9762] in
                      [uu____9760] in
                    let uu____9765 =
                      let uu____9766 =
                        let uu____9769 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9769, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9766 in
                    (uu____9757, [xx1], uu____9765) in
                  FStar_SMTEncoding_Util.mkExists uu____9751 in
                (uu____9750, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9747 in
            ([[l_exists_a_b]], [aa; bb], uu____9746) in
          FStar_SMTEncoding_Util.mkForall uu____9740 in
        (uu____9739, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9735 in
    [uu____9734] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9805 =
      let uu____9806 =
        let uu____9810 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9811 = varops.mk_unique "typing_range_const" in
        (uu____9810, (Some "Range_const typing"), uu____9811) in
      FStar_SMTEncoding_Util.mkAssume uu____9806 in
    [uu____9805] in
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
          let uu____10073 =
            FStar_Util.find_opt
              (fun uu____10091  ->
                 match uu____10091 with
                 | (l,uu____10101) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____10073 with
          | None  -> []
          | Some (uu____10123,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10160 = encode_function_type_as_formula t env in
        match uu____10160 with
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
            let uu____10192 =
              (let uu____10193 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10193) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10192
            then
              let uu____10197 = new_term_constant_and_tok_from_lid env lid in
              match uu____10197 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10209 =
                      let uu____10210 = FStar_Syntax_Subst.compress t_norm in
                      uu____10210.FStar_Syntax_Syntax.n in
                    match uu____10209 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10215) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10232  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10235 -> [] in
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
              (let uu____10244 = prims.is lid in
               if uu____10244
               then
                 let vname = varops.new_fvar lid in
                 let uu____10249 = prims.mk lid vname in
                 match uu____10249 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10264 =
                    let uu____10270 = curried_arrow_formals_comp t_norm in
                    match uu____10270 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10281 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10281
                          then
                            let uu____10282 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___145_10283 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___145_10283.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___145_10283.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___145_10283.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___145_10283.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___145_10283.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___145_10283.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___145_10283.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___145_10283.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___145_10283.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___145_10283.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___145_10283.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___145_10283.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___145_10283.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___145_10283.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___145_10283.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___145_10283.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___145_10283.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___145_10283.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___145_10283.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___145_10283.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___145_10283.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___145_10283.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___145_10283.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___145_10283.FStar_TypeChecker_Env.proof_ns)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10282
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10290 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10290)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10264 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10317 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10317 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10330 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___116_10354  ->
                                     match uu___116_10354 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10357 =
                                           FStar_Util.prefix vars in
                                         (match uu____10357 with
                                          | (uu____10368,(xxsym,uu____10370))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10380 =
                                                let uu____10381 =
                                                  let uu____10385 =
                                                    let uu____10386 =
                                                      let uu____10392 =
                                                        let uu____10393 =
                                                          let uu____10396 =
                                                            let uu____10397 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10397 in
                                                          (vapp, uu____10396) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10393 in
                                                      ([[vapp]], vars,
                                                        uu____10392) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10386 in
                                                  (uu____10385,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10381 in
                                              [uu____10380])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10408 =
                                           FStar_Util.prefix vars in
                                         (match uu____10408 with
                                          | (uu____10419,(xxsym,uu____10421))
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
                                              let uu____10435 =
                                                let uu____10436 =
                                                  let uu____10440 =
                                                    let uu____10441 =
                                                      let uu____10447 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10447) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10441 in
                                                  (uu____10440,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10436 in
                                              [uu____10435])
                                     | uu____10456 -> [])) in
                           let uu____10457 = encode_binders None formals env1 in
                           (match uu____10457 with
                            | (vars,guards,env',decls1,uu____10473) ->
                                let uu____10480 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10485 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10485, decls1)
                                  | Some p ->
                                      let uu____10487 = encode_formula p env' in
                                      (match uu____10487 with
                                       | (g,ds) ->
                                           let uu____10494 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10494,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10480 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10503 =
                                         let uu____10507 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10507) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10503 in
                                     let uu____10512 =
                                       let vname_decl =
                                         let uu____10517 =
                                           let uu____10523 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10528  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10523,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10517 in
                                       let uu____10533 =
                                         let env2 =
                                           let uu___146_10537 = env1 in
                                           {
                                             bindings =
                                               (uu___146_10537.bindings);
                                             depth = (uu___146_10537.depth);
                                             tcenv = (uu___146_10537.tcenv);
                                             warn = (uu___146_10537.warn);
                                             cache = (uu___146_10537.cache);
                                             nolabels =
                                               (uu___146_10537.nolabels);
                                             use_zfuel_name =
                                               (uu___146_10537.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___146_10537.current_module_name)
                                           } in
                                         let uu____10538 =
                                           let uu____10539 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10539 in
                                         if uu____10538
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10533 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10549::uu____10550 ->
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
                                                   let uu____10573 =
                                                     let uu____10579 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10579) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10573 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10593 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10595 =
                                             match formals with
                                             | [] ->
                                                 let uu____10604 =
                                                   let uu____10605 =
                                                     let uu____10607 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10607 in
                                                   push_free_var env1 lid
                                                     vname uu____10605 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10604)
                                             | uu____10610 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10615 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10615 in
                                                 let name_tok_corr =
                                                   let uu____10617 =
                                                     let uu____10621 =
                                                       let uu____10622 =
                                                         let uu____10628 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10628) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10622 in
                                                     (uu____10621,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10617 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10595 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10512 with
                                      | (decls2,env2) ->
                                          let uu____10652 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10657 =
                                              encode_term res_t1 env' in
                                            match uu____10657 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10665 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10665,
                                                  decls) in
                                          (match uu____10652 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10673 =
                                                   let uu____10677 =
                                                     let uu____10678 =
                                                       let uu____10684 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10684) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10678 in
                                                   (uu____10677,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10673 in
                                               let freshness =
                                                 let uu____10693 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10693
                                                 then
                                                   let uu____10696 =
                                                     let uu____10697 =
                                                       let uu____10703 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
                                                       let uu____10709 =
                                                         varops.next_id () in
                                                       (vname, uu____10703,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10709) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10697 in
                                                   let uu____10711 =
                                                     let uu____10713 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10713] in
                                                   uu____10696 :: uu____10711
                                                 else [] in
                                               let g =
                                                 let uu____10717 =
                                                   let uu____10719 =
                                                     let uu____10721 =
                                                       let uu____10723 =
                                                         let uu____10725 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10725 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10723 in
                                                     FStar_List.append decls3
                                                       uu____10721 in
                                                   FStar_List.append decls2
                                                     uu____10719 in
                                                 FStar_List.append decls11
                                                   uu____10717 in
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
          let uu____10747 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10747 with
          | None  ->
              let uu____10770 = encode_free_var env x t t_norm [] in
              (match uu____10770 with
               | (decls,env1) ->
                   let uu____10785 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10785 with
                    | (n1,x',uu____10804) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10816) -> ((n1, x1), [], env)
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
          let uu____10849 = encode_free_var env lid t tt quals in
          match uu____10849 with
          | (decls,env1) ->
              let uu____10860 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10860
              then
                let uu____10864 =
                  let uu____10866 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10866 in
                (uu____10864, env1)
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
             (fun uu____10894  ->
                fun lb  ->
                  match uu____10894 with
                  | (decls,env1) ->
                      let uu____10906 =
                        let uu____10910 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10910
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10906 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10924 = FStar_Syntax_Util.head_and_args t in
    match uu____10924 with
    | (hd1,args) ->
        let uu____10950 =
          let uu____10951 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10951.FStar_Syntax_Syntax.n in
        (match uu____10950 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10955,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10968 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10983  ->
      fun quals  ->
        match uu____10983 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____11032 = FStar_Util.first_N nbinders formals in
              match uu____11032 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11072  ->
                         fun uu____11073  ->
                           match (uu____11072, uu____11073) with
                           | ((formal,uu____11083),(binder,uu____11085)) ->
                               let uu____11090 =
                                 let uu____11095 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11095) in
                               FStar_Syntax_Syntax.NT uu____11090) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11100 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11114  ->
                              match uu____11114 with
                              | (x,i) ->
                                  let uu____11121 =
                                    let uu___147_11122 = x in
                                    let uu____11123 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___147_11122.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___147_11122.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11123
                                    } in
                                  (uu____11121, i))) in
                    FStar_All.pipe_right uu____11100
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11135 =
                      let uu____11137 =
                        let uu____11138 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11138.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____11137 in
                    let uu____11142 =
                      let uu____11143 = FStar_Syntax_Subst.compress body in
                      let uu____11144 =
                        let uu____11145 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11145 in
                      FStar_Syntax_Syntax.extend_app_n uu____11143
                        uu____11144 in
                    uu____11142 uu____11135 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11187 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11187
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___148_11188 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___148_11188.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___148_11188.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___148_11188.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___148_11188.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___148_11188.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___148_11188.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___148_11188.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___148_11188.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___148_11188.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___148_11188.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___148_11188.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___148_11188.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___148_11188.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___148_11188.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___148_11188.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___148_11188.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___148_11188.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___148_11188.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___148_11188.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___148_11188.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___148_11188.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___148_11188.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___148_11188.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___148_11188.FStar_TypeChecker_Env.proof_ns)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11209 = FStar_Syntax_Util.abs_formals e in
                match uu____11209 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11258::uu____11259 ->
                         let uu____11267 =
                           let uu____11268 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11268.FStar_Syntax_Syntax.n in
                         (match uu____11267 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11295 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11295 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11321 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11321
                                   then
                                     let uu____11339 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11339 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11385  ->
                                                   fun uu____11386  ->
                                                     match (uu____11385,
                                                             uu____11386)
                                                     with
                                                     | ((x,uu____11396),
                                                        (b,uu____11398)) ->
                                                         let uu____11403 =
                                                           let uu____11408 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11408) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11403)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11410 =
                                            let uu____11421 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11421) in
                                          (uu____11410, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11456 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11456 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11508) ->
                              let uu____11513 =
                                let uu____11524 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____11524 in
                              (uu____11513, true)
                          | uu____11557 when Prims.op_Negation norm1 ->
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
                          | uu____11559 ->
                              let uu____11560 =
                                let uu____11561 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11562 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11561
                                  uu____11562 in
                              failwith uu____11560)
                     | uu____11575 ->
                         let uu____11576 =
                           let uu____11577 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11577.FStar_Syntax_Syntax.n in
                         (match uu____11576 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11604 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11604 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11622 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11622 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11670 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11698 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11698
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11705 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11746  ->
                            fun lb  ->
                              match uu____11746 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11797 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11797
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11800 =
                                      let uu____11808 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11808
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11800 with
                                    | (tok,decl,env2) ->
                                        let uu____11833 =
                                          let uu____11840 =
                                            let uu____11846 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11846, tok) in
                                          uu____11840 :: toks in
                                        (uu____11833, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11705 with
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
                        | uu____11948 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11953 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11953 vars)
                            else
                              (let uu____11955 =
                                 let uu____11959 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11959) in
                               FStar_SMTEncoding_Util.mkApp uu____11955) in
                      let uu____11964 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___117_11966  ->
                                 match uu___117_11966 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11967 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11970 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11970))) in
                      if uu____11964
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11990;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11992;
                                FStar_Syntax_Syntax.lbeff = uu____11993;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____12034 =
                                 let uu____12038 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____12038 with
                                 | (tcenv',uu____12049,e_t) ->
                                     let uu____12053 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12060 -> failwith "Impossible" in
                                     (match uu____12053 with
                                      | (e1,t_norm1) ->
                                          ((let uu___151_12069 = env1 in
                                            {
                                              bindings =
                                                (uu___151_12069.bindings);
                                              depth = (uu___151_12069.depth);
                                              tcenv = tcenv';
                                              warn = (uu___151_12069.warn);
                                              cache = (uu___151_12069.cache);
                                              nolabels =
                                                (uu___151_12069.nolabels);
                                              use_zfuel_name =
                                                (uu___151_12069.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___151_12069.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___151_12069.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____12034 with
                                | (env',e1,t_norm1) ->
                                    let uu____12076 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____12076 with
                                     | ((binders,body,uu____12088,uu____12089),curry)
                                         ->
                                         ((let uu____12096 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____12096
                                           then
                                             let uu____12097 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12098 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12097 uu____12098
                                           else ());
                                          (let uu____12100 =
                                             encode_binders None binders env' in
                                           match uu____12100 with
                                           | (vars,guards,env'1,binder_decls,uu____12116)
                                               ->
                                               let body1 =
                                                 let uu____12124 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12124
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12127 =
                                                 let uu____12132 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12132
                                                 then
                                                   let uu____12138 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12139 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12138, uu____12139)
                                                 else
                                                   (let uu____12145 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12145)) in
                                               (match uu____12127 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12159 =
                                                        let uu____12163 =
                                                          let uu____12164 =
                                                            let uu____12170 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12170) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12164 in
                                                        let uu____12176 =
                                                          let uu____12178 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12178 in
                                                        (uu____12163,
                                                          uu____12176,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12159 in
                                                    let uu____12180 =
                                                      let uu____12182 =
                                                        let uu____12184 =
                                                          let uu____12186 =
                                                            let uu____12188 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12188 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12186 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12184 in
                                                      FStar_List.append
                                                        decls1 uu____12182 in
                                                    (uu____12180, env1))))))
                           | uu____12191 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12210 = varops.fresh "fuel" in
                             (uu____12210, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12213 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12252  ->
                                     fun uu____12253  ->
                                       match (uu____12252, uu____12253) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12335 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12335 in
                                           let gtok =
                                             let uu____12337 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12337 in
                                           let env3 =
                                             let uu____12339 =
                                               let uu____12341 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12341 in
                                             push_free_var env2 flid gtok
                                               uu____12339 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12213 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12427
                                 t_norm uu____12429 =
                                 match (uu____12427, uu____12429) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12456;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12457;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12474 =
                                       let uu____12478 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12478 with
                                       | (tcenv',uu____12493,e_t) ->
                                           let uu____12497 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12504 ->
                                                 failwith "Impossible" in
                                           (match uu____12497 with
                                            | (e1,t_norm1) ->
                                                ((let uu___152_12513 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___152_12513.bindings);
                                                    depth =
                                                      (uu___152_12513.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___152_12513.warn);
                                                    cache =
                                                      (uu___152_12513.cache);
                                                    nolabels =
                                                      (uu___152_12513.nolabels);
                                                    use_zfuel_name =
                                                      (uu___152_12513.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___152_12513.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___152_12513.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12474 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12523 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12523
                                            then
                                              let uu____12524 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12525 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12526 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12524 uu____12525
                                                uu____12526
                                            else ());
                                           (let uu____12528 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12528 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12550 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12550
                                                  then
                                                    let uu____12551 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12552 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12553 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12554 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12551 uu____12552
                                                      uu____12553 uu____12554
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12558 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12558 with
                                                  | (vars,guards,env'1,binder_decls,uu____12576)
                                                      ->
                                                      let decl_g =
                                                        let uu____12584 =
                                                          let uu____12590 =
                                                            let uu____12592 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12592 in
                                                          (g, uu____12590,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12584 in
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
                                                        let uu____12607 =
                                                          let uu____12611 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12611) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12607 in
                                                      let gsapp =
                                                        let uu____12617 =
                                                          let uu____12621 =
                                                            let uu____12623 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12623 ::
                                                              vars_tm in
                                                          (g, uu____12621) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12617 in
                                                      let gmax =
                                                        let uu____12627 =
                                                          let uu____12631 =
                                                            let uu____12633 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12633 ::
                                                              vars_tm in
                                                          (g, uu____12631) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12627 in
                                                      let body1 =
                                                        let uu____12637 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12637
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12639 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12639 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12650
                                                               =
                                                               let uu____12654
                                                                 =
                                                                 let uu____12655
                                                                   =
                                                                   let uu____12663
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
                                                                    uu____12663) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12655 in
                                                               let uu____12674
                                                                 =
                                                                 let uu____12676
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12676 in
                                                               (uu____12654,
                                                                 uu____12674,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12650 in
                                                           let eqn_f =
                                                             let uu____12679
                                                               =
                                                               let uu____12683
                                                                 =
                                                                 let uu____12684
                                                                   =
                                                                   let uu____12690
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12690) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12684 in
                                                               (uu____12683,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12679 in
                                                           let eqn_g' =
                                                             let uu____12698
                                                               =
                                                               let uu____12702
                                                                 =
                                                                 let uu____12703
                                                                   =
                                                                   let uu____12709
                                                                    =
                                                                    let uu____12710
                                                                    =
                                                                    let uu____12713
                                                                    =
                                                                    let uu____12714
                                                                    =
                                                                    let uu____12718
                                                                    =
                                                                    let uu____12720
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12720
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12718) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12714 in
                                                                    (gsapp,
                                                                    uu____12713) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12710 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12709) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12703 in
                                                               (uu____12702,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12698 in
                                                           let uu____12732 =
                                                             let uu____12737
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12737
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12754)
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
                                                                    let uu____12769
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12769
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12772
                                                                    =
                                                                    let uu____12776
                                                                    =
                                                                    let uu____12777
                                                                    =
                                                                    let uu____12783
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12783) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12777 in
                                                                    (uu____12776,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12772 in
                                                                 let uu____12794
                                                                   =
                                                                   let uu____12798
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12798
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12806
                                                                    =
                                                                    let uu____12808
                                                                    =
                                                                    let uu____12809
                                                                    =
                                                                    let uu____12813
                                                                    =
                                                                    let uu____12814
                                                                    =
                                                                    let uu____12820
                                                                    =
                                                                    let uu____12821
                                                                    =
                                                                    let uu____12824
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12824,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12821 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12820) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12814 in
                                                                    (uu____12813,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12809 in
                                                                    [uu____12808] in
                                                                    (d3,
                                                                    uu____12806) in
                                                                 (match uu____12794
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12732
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
                               let uu____12859 =
                                 let uu____12866 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12902  ->
                                      fun uu____12903  ->
                                        match (uu____12902, uu____12903) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12989 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12989 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12866 in
                               (match uu____12859 with
                                | (decls2,eqns,env01) ->
                                    let uu____13029 =
                                      let isDeclFun uu___118_13037 =
                                        match uu___118_13037 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____13038 -> true
                                        | uu____13044 -> false in
                                      let uu____13045 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____13045
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____13029 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____13072 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____13072
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
        let uu____13105 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13105 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____13108 = encode_sigelt' env se in
      match uu____13108 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13118 =
                  let uu____13119 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13119 in
                [uu____13118]
            | uu____13120 ->
                let uu____13121 =
                  let uu____13123 =
                    let uu____13124 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13124 in
                  uu____13123 :: g in
                let uu____13125 =
                  let uu____13127 =
                    let uu____13128 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13128 in
                  [uu____13127] in
                FStar_List.append uu____13121 uu____13125 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13136 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13139 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13141 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13143 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13151 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13154 =
            let uu____13155 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13155 Prims.op_Negation in
          if uu____13154
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13175 ->
                   let uu____13176 =
                     let uu____13179 =
                       let uu____13180 =
                         let uu____13195 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13195) in
                       FStar_Syntax_Syntax.Tm_abs uu____13180 in
                     FStar_Syntax_Syntax.mk uu____13179 in
                   uu____13176 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13248 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13248 with
               | (aname,atok,env2) ->
                   let uu____13258 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13258 with
                    | (formals,uu____13268) ->
                        let uu____13275 =
                          let uu____13278 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13278 env2 in
                        (match uu____13275 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13286 =
                                 let uu____13287 =
                                   let uu____13293 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13301  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13293,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13287 in
                               [uu____13286;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13308 =
                               let aux uu____13337 uu____13338 =
                                 match (uu____13337, uu____13338) with
                                 | ((bv,uu____13365),(env3,acc_sorts,acc)) ->
                                     let uu____13386 = gen_term_var env3 bv in
                                     (match uu____13386 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13308 with
                              | (uu____13424,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13438 =
                                      let uu____13442 =
                                        let uu____13443 =
                                          let uu____13449 =
                                            let uu____13450 =
                                              let uu____13453 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13453) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13450 in
                                          ([[app]], xs_sorts, uu____13449) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13443 in
                                      (uu____13442, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13438 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13465 =
                                      let uu____13469 =
                                        let uu____13470 =
                                          let uu____13476 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13476) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13470 in
                                      (uu____13469,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13465 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13486 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13486 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13502,uu____13503)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13504 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13504 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13515,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13520 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___119_13522  ->
                      match uu___119_13522 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13523 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13526 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13527 -> false)) in
            Prims.op_Negation uu____13520 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13533 = encode_top_level_val env fv t quals in
             match uu____13533 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13545 =
                   let uu____13547 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13547 in
                 (uu____13545, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13552 = encode_formula f env in
          (match uu____13552 with
           | (f1,decls) ->
               let g =
                 let uu____13561 =
                   let uu____13562 =
                     let uu____13566 =
                       let uu____13568 =
                         let uu____13569 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13569 in
                       Some uu____13568 in
                     let uu____13570 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13566, uu____13570) in
                   FStar_SMTEncoding_Util.mkAssume uu____13562 in
                 [uu____13561] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13574,uu____13575) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13581 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13588 =
                       let uu____13593 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13593.FStar_Syntax_Syntax.fv_name in
                     uu____13588.FStar_Syntax_Syntax.v in
                   let uu____13597 =
                     let uu____13598 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13598 in
                   if uu____13597
                   then
                     let val_decl =
                       let uu___153_13613 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___153_13613.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___153_13613.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___153_13613.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13617 = encode_sigelt' env1 val_decl in
                     match uu____13617 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____13581 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13634,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13636;
                          FStar_Syntax_Syntax.lbtyp = uu____13637;
                          FStar_Syntax_Syntax.lbeff = uu____13638;
                          FStar_Syntax_Syntax.lbdef = uu____13639;_}::[]),uu____13640,uu____13641)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13655 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13655 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13678 =
                   let uu____13680 =
                     let uu____13681 =
                       let uu____13685 =
                         let uu____13686 =
                           let uu____13692 =
                             let uu____13693 =
                               let uu____13696 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13696) in
                             FStar_SMTEncoding_Util.mkEq uu____13693 in
                           ([[b2t_x]], [xx], uu____13692) in
                         FStar_SMTEncoding_Util.mkForall uu____13686 in
                       (uu____13685, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13681 in
                   [uu____13680] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13678 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13713,uu____13714,uu____13715)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___120_13721  ->
                  match uu___120_13721 with
                  | FStar_Syntax_Syntax.Discriminator uu____13722 -> true
                  | uu____13723 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13725,lids,uu____13727) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13734 =
                     let uu____13735 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13735.FStar_Ident.idText in
                   uu____13734 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___121_13737  ->
                     match uu___121_13737 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13738 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13741,uu____13742)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___122_13752  ->
                  match uu___122_13752 with
                  | FStar_Syntax_Syntax.Projector uu____13753 -> true
                  | uu____13756 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13763 = try_lookup_free_var env l in
          (match uu____13763 with
           | Some uu____13767 -> ([], env)
           | None  ->
               let se1 =
                 let uu___154_13770 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___154_13770.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___154_13770.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13776,uu____13777) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13789) ->
          let uu____13794 = encode_sigelts env ses in
          (match uu____13794 with
           | (g,env1) ->
               let uu____13804 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___123_13814  ->
                         match uu___123_13814 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13815;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13816;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13817;_}
                             -> false
                         | uu____13819 -> true)) in
               (match uu____13804 with
                | (g',inversions) ->
                    let uu____13828 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___124_13838  ->
                              match uu___124_13838 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13839 ->
                                  true
                              | uu____13845 -> false)) in
                    (match uu____13828 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13856,tps,k,uu____13859,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___125_13869  ->
                    match uu___125_13869 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13870 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13877 = c in
              match uu____13877 with
              | (name,args,uu____13881,uu____13882,uu____13883) ->
                  let uu____13886 =
                    let uu____13887 =
                      let uu____13893 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13900  ->
                                match uu____13900 with
                                | (uu____13904,sort,uu____13906) -> sort)) in
                      (name, uu____13893, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13887 in
                  [uu____13886]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13924 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13927 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13927 FStar_Option.isNone)) in
            if uu____13924
            then []
            else
              (let uu____13944 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13944 with
               | (xxsym,xx) ->
                   let uu____13950 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13961  ->
                             fun l  ->
                               match uu____13961 with
                               | (out,decls) ->
                                   let uu____13973 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13973 with
                                    | (uu____13979,data_t) ->
                                        let uu____13981 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13981 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____14010 =
                                                 let uu____14011 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____14011.FStar_Syntax_Syntax.n in
                                               match uu____14010 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____14019,indices) ->
                                                   indices
                                               | uu____14035 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____14047  ->
                                                         match uu____14047
                                                         with
                                                         | (x,uu____14051) ->
                                                             let uu____14052
                                                               =
                                                               let uu____14053
                                                                 =
                                                                 let uu____14057
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____14057,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14053 in
                                                             push_term_var
                                                               env1 x
                                                               uu____14052)
                                                    env) in
                                             let uu____14059 =
                                               encode_args indices env1 in
                                             (match uu____14059 with
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
                                                      let uu____14079 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14087
                                                                 =
                                                                 let uu____14090
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____14090,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14087)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____14079
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____14092 =
                                                      let uu____14093 =
                                                        let uu____14096 =
                                                          let uu____14097 =
                                                            let uu____14100 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____14100,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14097 in
                                                        (out, uu____14096) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14093 in
                                                    (uu____14092,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13950 with
                    | (data_ax,decls) ->
                        let uu____14108 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14108 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14119 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14119 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
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
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14133,
                                       uu____14141) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14127 in
                                 let uu____14149 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14126, (Some "inversion axiom"),
                                   uu____14149) in
                               FStar_SMTEncoding_Util.mkAssume uu____14122 in
                             let pattern_guarded_inversion =
                               let uu____14153 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14153
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14161 =
                                   let uu____14162 =
                                     let uu____14166 =
                                       let uu____14167 =
                                         let uu____14173 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14181 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14173, uu____14181) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14167 in
                                     let uu____14189 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14166, (Some "inversion axiom"),
                                       uu____14189) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14162 in
                                 [uu____14161]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14192 =
            let uu____14200 =
              let uu____14201 = FStar_Syntax_Subst.compress k in
              uu____14201.FStar_Syntax_Syntax.n in
            match uu____14200 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14230 -> (tps, k) in
          (match uu____14192 with
           | (formals,res) ->
               let uu____14245 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14245 with
                | (formals1,res1) ->
                    let uu____14252 = encode_binders None formals1 env in
                    (match uu____14252 with
                     | (vars,guards,env',binder_decls,uu____14267) ->
                         let uu____14274 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14274 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14287 =
                                  let uu____14291 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14291) in
                                FStar_SMTEncoding_Util.mkApp uu____14287 in
                              let uu____14296 =
                                let tname_decl =
                                  let uu____14302 =
                                    let uu____14303 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14318  ->
                                              match uu____14318 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14326 = varops.next_id () in
                                    (tname, uu____14303,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14326, false) in
                                  constructor_or_logic_type_decl uu____14302 in
                                let uu____14331 =
                                  match vars with
                                  | [] ->
                                      let uu____14338 =
                                        let uu____14339 =
                                          let uu____14341 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14341 in
                                        push_free_var env1 t tname
                                          uu____14339 in
                                      ([], uu____14338)
                                  | uu____14345 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14351 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14351 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14360 =
                                          let uu____14364 =
                                            let uu____14365 =
                                              let uu____14373 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14373) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14365 in
                                          (uu____14364,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14360 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14331 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14296 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14396 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14396 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14410 =
                                               let uu____14411 =
                                                 let uu____14415 =
                                                   let uu____14416 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14416 in
                                                 (uu____14415,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14411 in
                                             [uu____14410]
                                           else [] in
                                         let uu____14419 =
                                           let uu____14421 =
                                             let uu____14423 =
                                               let uu____14424 =
                                                 let uu____14428 =
                                                   let uu____14429 =
                                                     let uu____14435 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14435) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14429 in
                                                 (uu____14428, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14424 in
                                             [uu____14423] in
                                           FStar_List.append karr uu____14421 in
                                         FStar_List.append decls1 uu____14419 in
                                   let aux =
                                     let uu____14444 =
                                       let uu____14446 =
                                         inversion_axioms tapp vars in
                                       let uu____14448 =
                                         let uu____14450 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14450] in
                                       FStar_List.append uu____14446
                                         uu____14448 in
                                     FStar_List.append kindingAx uu____14444 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14455,uu____14456,uu____14457,uu____14458,uu____14459)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14464,t,uu____14466,n_tps,uu____14468) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14473 = new_term_constant_and_tok_from_lid env d in
          (match uu____14473 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14484 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14484 with
                | (formals,t_res) ->
                    let uu____14506 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14506 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14515 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14515 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14553 =
                                            mk_term_projector_name d x in
                                          (uu____14553,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14555 =
                                  let uu____14565 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14565, true) in
                                FStar_All.pipe_right uu____14555
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
                              let uu____14587 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14587 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14595::uu____14596 ->
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
                                         let uu____14621 =
                                           let uu____14627 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14627) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14621
                                     | uu____14640 -> tok_typing in
                                   let uu____14645 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14645 with
                                    | (vars',guards',env'',decls_formals,uu____14660)
                                        ->
                                        let uu____14667 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14667 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14686 ->
                                                   let uu____14690 =
                                                     let uu____14691 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14691 in
                                                   [uu____14690] in
                                             let encode_elim uu____14698 =
                                               let uu____14699 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14699 with
                                               | (head1,args) ->
                                                   let uu____14728 =
                                                     let uu____14729 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14729.FStar_Syntax_Syntax.n in
                                                   (match uu____14728 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____14736;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14737;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14738;_},uu____14739)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14749 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14749
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
                                                                 | uu____14775
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14783
                                                                    =
                                                                    let uu____14784
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14784 in
                                                                    if
                                                                    uu____14783
                                                                    then
                                                                    let uu____14791
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14791]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14793
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14806
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14806
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14828
                                                                    =
                                                                    let uu____14832
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14832 in
                                                                    (match uu____14828
                                                                    with
                                                                    | 
                                                                    (uu____14839,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14845
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14845
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14847
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14847
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
                                                             (match uu____14793
                                                              with
                                                              | (uu____14855,arg_vars,elim_eqns_or_guards,uu____14858)
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
                                                                    let uu____14877
                                                                    =
                                                                    let uu____14881
                                                                    =
                                                                    let uu____14882
                                                                    =
                                                                    let uu____14888
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14894
                                                                    =
                                                                    let uu____14895
                                                                    =
                                                                    let uu____14898
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14898) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14895 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14888,
                                                                    uu____14894) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14882 in
                                                                    (uu____14881,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14877 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14911
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14911,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14913
                                                                    =
                                                                    let uu____14917
                                                                    =
                                                                    let uu____14918
                                                                    =
                                                                    let uu____14924
                                                                    =
                                                                    let uu____14927
                                                                    =
                                                                    let uu____14929
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14929] in
                                                                    [uu____14927] in
                                                                    let uu____14932
                                                                    =
                                                                    let uu____14933
                                                                    =
                                                                    let uu____14936
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14937
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14936,
                                                                    uu____14937) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14933 in
                                                                    (uu____14924,
                                                                    [x],
                                                                    uu____14932) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14918 in
                                                                    let uu____14947
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14917,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14947) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14913
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14952
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
                                                                    (let uu____14967
                                                                    =
                                                                    let uu____14968
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14968
                                                                    dapp1 in
                                                                    [uu____14967]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14952
                                                                    FStar_List.flatten in
                                                                    let uu____14972
                                                                    =
                                                                    let uu____14976
                                                                    =
                                                                    let uu____14977
                                                                    =
                                                                    let uu____14983
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14989
                                                                    =
                                                                    let uu____14990
                                                                    =
                                                                    let uu____14993
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14993) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14990 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14983,
                                                                    uu____14989) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14977 in
                                                                    (uu____14976,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14972) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____15009 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15009
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
                                                                 | uu____15035
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15043
                                                                    =
                                                                    let uu____15044
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15044 in
                                                                    if
                                                                    uu____15043
                                                                    then
                                                                    let uu____15051
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15051]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15053
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15066
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15066
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15088
                                                                    =
                                                                    let uu____15092
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15092 in
                                                                    (match uu____15088
                                                                    with
                                                                    | 
                                                                    (uu____15099,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15105
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15105
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15107
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15107
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
                                                             (match uu____15053
                                                              with
                                                              | (uu____15115,arg_vars,elim_eqns_or_guards,uu____15118)
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
                                                                    let uu____15137
                                                                    =
                                                                    let uu____15141
                                                                    =
                                                                    let uu____15142
                                                                    =
                                                                    let uu____15148
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15154
                                                                    =
                                                                    let uu____15155
                                                                    =
                                                                    let uu____15158
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15158) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15155 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15148,
                                                                    uu____15154) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15142 in
                                                                    (uu____15141,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15137 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15171
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15171,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15173
                                                                    =
                                                                    let uu____15177
                                                                    =
                                                                    let uu____15178
                                                                    =
                                                                    let uu____15184
                                                                    =
                                                                    let uu____15187
                                                                    =
                                                                    let uu____15189
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15189] in
                                                                    [uu____15187] in
                                                                    let uu____15192
                                                                    =
                                                                    let uu____15193
                                                                    =
                                                                    let uu____15196
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15197
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15196,
                                                                    uu____15197) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15193 in
                                                                    (uu____15184,
                                                                    [x],
                                                                    uu____15192) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15178 in
                                                                    let uu____15207
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15177,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15207) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15173
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15212
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
                                                                    (let uu____15227
                                                                    =
                                                                    let uu____15228
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15228
                                                                    dapp1 in
                                                                    [uu____15227]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15212
                                                                    FStar_List.flatten in
                                                                    let uu____15232
                                                                    =
                                                                    let uu____15236
                                                                    =
                                                                    let uu____15237
                                                                    =
                                                                    let uu____15243
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15249
                                                                    =
                                                                    let uu____15250
                                                                    =
                                                                    let uu____15253
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15253) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15250 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15243,
                                                                    uu____15249) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15237 in
                                                                    (uu____15236,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15232) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15263 ->
                                                        ((let uu____15265 =
                                                            let uu____15266 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15267 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15266
                                                              uu____15267 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15265);
                                                         ([], []))) in
                                             let uu____15270 = encode_elim () in
                                             (match uu____15270 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15282 =
                                                      let uu____15284 =
                                                        let uu____15286 =
                                                          let uu____15288 =
                                                            let uu____15290 =
                                                              let uu____15291
                                                                =
                                                                let uu____15297
                                                                  =
                                                                  let uu____15299
                                                                    =
                                                                    let uu____15300
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15300 in
                                                                  Some
                                                                    uu____15299 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15297) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15291 in
                                                            [uu____15290] in
                                                          let uu____15303 =
                                                            let uu____15305 =
                                                              let uu____15307
                                                                =
                                                                let uu____15309
                                                                  =
                                                                  let uu____15311
                                                                    =
                                                                    let uu____15313
                                                                    =
                                                                    let uu____15315
                                                                    =
                                                                    let uu____15316
                                                                    =
                                                                    let uu____15320
                                                                    =
                                                                    let uu____15321
                                                                    =
                                                                    let uu____15327
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15327) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15321 in
                                                                    (uu____15320,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15316 in
                                                                    let uu____15334
                                                                    =
                                                                    let uu____15336
                                                                    =
                                                                    let uu____15337
                                                                    =
                                                                    let uu____15341
                                                                    =
                                                                    let uu____15342
                                                                    =
                                                                    let uu____15348
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____15354
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15348,
                                                                    uu____15354) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15342 in
                                                                    (uu____15341,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15337 in
                                                                    [uu____15336] in
                                                                    uu____15315
                                                                    ::
                                                                    uu____15334 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15313 in
                                                                  FStar_List.append
                                                                    uu____15311
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15309 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15307 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15305 in
                                                          FStar_List.append
                                                            uu____15288
                                                            uu____15303 in
                                                        FStar_List.append
                                                          decls3 uu____15286 in
                                                      FStar_List.append
                                                        decls2 uu____15284 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15282 in
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
           (fun uu____15375  ->
              fun se  ->
                match uu____15375 with
                | (g,env1) ->
                    let uu____15387 = encode_sigelt env1 se in
                    (match uu____15387 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15423 =
        match uu____15423 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15441 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____15446 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15446
                   then
                     let uu____15447 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15448 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15449 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15447 uu____15448 uu____15449
                   else ());
                  (let uu____15451 = encode_term t1 env1 in
                   match uu____15451 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15461 =
                         let uu____15465 =
                           let uu____15466 =
                             let uu____15467 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15467
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15466 in
                         new_term_constant_from_string env1 x uu____15465 in
                       (match uu____15461 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15478 = FStar_Options.log_queries () in
                              if uu____15478
                              then
                                let uu____15480 =
                                  let uu____15481 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15482 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15483 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15481 uu____15482 uu____15483 in
                                Some uu____15480
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15494,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15503 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15503 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15516,se,uu____15518) ->
                 let uu____15521 = encode_sigelt env1 se in
                 (match uu____15521 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15531,se) ->
                 let uu____15535 = encode_sigelt env1 se in
                 (match uu____15535 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15545 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15545 with | (uu____15557,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15602  ->
            match uu____15602 with
            | (l,uu____15609,uu____15610) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15631  ->
            match uu____15631 with
            | (l,uu____15639,uu____15640) ->
                let uu____15645 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39) (
                    fst l) in
                let uu____15646 =
                  let uu____15648 =
                    let uu____15649 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15649 in
                  [uu____15648] in
                uu____15645 :: uu____15646)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15660 =
      let uu____15662 =
        let uu____15663 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15665 =
          let uu____15666 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15666 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15663;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15665
        } in
      [uu____15662] in
    FStar_ST.write last_env uu____15660
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15676 = FStar_ST.read last_env in
      match uu____15676 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15682 ->
          let uu___155_15684 = e in
          let uu____15685 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___155_15684.bindings);
            depth = (uu___155_15684.depth);
            tcenv;
            warn = (uu___155_15684.warn);
            cache = (uu___155_15684.cache);
            nolabels = (uu___155_15684.nolabels);
            use_zfuel_name = (uu___155_15684.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_15684.encode_non_total_function_typ);
            current_module_name = uu____15685
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15689 = FStar_ST.read last_env in
    match uu____15689 with
    | [] -> failwith "Empty env stack"
    | uu____15694::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15702  ->
    let uu____15703 = FStar_ST.read last_env in
    match uu____15703 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___156_15714 = hd1 in
          {
            bindings = (uu___156_15714.bindings);
            depth = (uu___156_15714.depth);
            tcenv = (uu___156_15714.tcenv);
            warn = (uu___156_15714.warn);
            cache = refs;
            nolabels = (uu___156_15714.nolabels);
            use_zfuel_name = (uu___156_15714.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___156_15714.encode_non_total_function_typ);
            current_module_name = (uu___156_15714.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15720  ->
    let uu____15721 = FStar_ST.read last_env in
    match uu____15721 with
    | [] -> failwith "Popping an empty stack"
    | uu____15726::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15734  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15737  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15740  ->
    let uu____15741 = FStar_ST.read last_env in
    match uu____15741 with
    | hd1::uu____15747::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15753 -> failwith "Impossible"
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
        | (uu____15802::uu____15803,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___157_15807 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___157_15807.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___157_15807.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___157_15807.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15808 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15819 =
        let uu____15821 =
          let uu____15822 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15822 in
        let uu____15823 = open_fact_db_tags env in uu____15821 :: uu____15823 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15819
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
      let uu____15838 = encode_sigelt env se in
      match uu____15838 with
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
        let uu____15863 = FStar_Options.log_queries () in
        if uu____15863
        then
          let uu____15865 =
            let uu____15866 =
              let uu____15867 =
                let uu____15868 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15868 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15867 in
            FStar_SMTEncoding_Term.Caption uu____15866 in
          uu____15865 :: decls
        else decls in
      let env =
        let uu____15875 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15875 tcenv in
      let uu____15876 = encode_top_level_facts env se in
      match uu____15876 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15885 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15885))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15896 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15896
       then
         let uu____15897 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15897
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15918  ->
                 fun se  ->
                   match uu____15918 with
                   | (g,env2) ->
                       let uu____15930 = encode_top_level_facts env2 se in
                       (match uu____15930 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15943 =
         encode_signature
           (let uu___158_15947 = env in
            {
              bindings = (uu___158_15947.bindings);
              depth = (uu___158_15947.depth);
              tcenv = (uu___158_15947.tcenv);
              warn = false;
              cache = (uu___158_15947.cache);
              nolabels = (uu___158_15947.nolabels);
              use_zfuel_name = (uu___158_15947.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___158_15947.encode_non_total_function_typ);
              current_module_name = (uu___158_15947.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15943 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15959 = FStar_Options.log_queries () in
             if uu____15959
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___159_15964 = env1 in
               {
                 bindings = (uu___159_15964.bindings);
                 depth = (uu___159_15964.depth);
                 tcenv = (uu___159_15964.tcenv);
                 warn = true;
                 cache = (uu___159_15964.cache);
                 nolabels = (uu___159_15964.nolabels);
                 use_zfuel_name = (uu___159_15964.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___159_15964.encode_non_total_function_typ);
                 current_module_name = (uu___159_15964.current_module_name)
               });
            (let uu____15966 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15966
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
        (let uu____16001 =
           let uu____16002 = FStar_TypeChecker_Env.current_module tcenv in
           uu____16002.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16001);
        (let env =
           let uu____16004 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____16004 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____16011 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16032 = aux rest in
                 (match uu____16032 with
                  | (out,rest1) ->
                      let t =
                        let uu____16050 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____16050 with
                        | Some uu____16054 ->
                            let uu____16055 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16055
                              x.FStar_Syntax_Syntax.sort
                        | uu____16056 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____16059 =
                        let uu____16061 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___160_16062 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___160_16062.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___160_16062.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16061 :: out in
                      (uu____16059, rest1))
             | uu____16065 -> ([], bindings1) in
           let uu____16069 = aux bindings in
           match uu____16069 with
           | (closing,bindings1) ->
               let uu____16083 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16083, bindings1) in
         match uu____16011 with
         | (q1,bindings1) ->
             let uu____16096 =
               let uu____16099 =
                 FStar_List.filter
                   (fun uu___126_16101  ->
                      match uu___126_16101 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16102 ->
                          false
                      | uu____16106 -> true) bindings1 in
               encode_env_bindings env uu____16099 in
             (match uu____16096 with
              | (env_decls,env1) ->
                  ((let uu____16117 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16117
                    then
                      let uu____16118 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16118
                    else ());
                   (let uu____16120 = encode_formula q1 env1 in
                    match uu____16120 with
                    | (phi,qdecls) ->
                        let uu____16132 =
                          let uu____16135 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16135 phi in
                        (match uu____16132 with
                         | (labels,phi1) ->
                             let uu____16145 = encode_labels labels in
                             (match uu____16145 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____16166 =
                                      let uu____16170 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16171 =
                                        varops.mk_unique "@query" in
                                      (uu____16170, (Some "query"),
                                        uu____16171) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16166 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16184 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16184 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16186 = encode_formula q env in
       match uu____16186 with
       | (f,uu____16190) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16192) -> true
             | uu____16195 -> false)))