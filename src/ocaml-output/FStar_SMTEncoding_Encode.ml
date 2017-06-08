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
        let uu___125_140 = a in
        let uu____141 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___125_140.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___125_140.FStar_Syntax_Syntax.sort)
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
  let new_scope uu____433 =
    let uu____434 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____436 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____434, uu____436) in
  let scopes =
    let uu____447 = let uu____453 = new_scope () in [uu____453] in
    FStar_Util.mk_ref uu____447 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____478 =
        let uu____480 = FStar_ST.read scopes in
        FStar_Util.find_map uu____480
          (fun uu____497  ->
             match uu____497 with
             | (names1,uu____504) -> FStar_Util.smap_try_find names1 y1) in
      match uu____478 with
      | None  -> y1
      | Some uu____509 ->
          (FStar_Util.incr ctr;
           (let uu____514 =
              let uu____515 =
                let uu____516 = FStar_ST.read ctr in
                Prims.string_of_int uu____516 in
              Prims.strcat "__" uu____515 in
            Prims.strcat y1 uu____514)) in
    let top_scope =
      let uu____521 =
        let uu____526 = FStar_ST.read scopes in FStar_List.hd uu____526 in
      FStar_All.pipe_left FStar_Pervasives.fst uu____521 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____565 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____576 =
      let uu____577 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____577 in
    FStar_Util.format2 "%s_%s" pfx uu____576 in
  let string_const s =
    let uu____582 =
      let uu____584 = FStar_ST.read scopes in
      FStar_Util.find_map uu____584
        (fun uu____601  ->
           match uu____601 with
           | (uu____607,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____582 with
    | Some f -> f
    | None  ->
        let id = next_id1 () in
        let f =
          let uu____616 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____616 in
        let top_scope =
          let uu____619 =
            let uu____624 = FStar_ST.read scopes in FStar_List.hd uu____624 in
          FStar_All.pipe_left FStar_Pervasives.snd uu____619 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____652 =
    let uu____653 =
      let uu____659 = new_scope () in
      let uu____664 = FStar_ST.read scopes in uu____659 :: uu____664 in
    FStar_ST.write scopes uu____653 in
  let pop1 uu____691 =
    let uu____692 =
      let uu____698 = FStar_ST.read scopes in FStar_List.tl uu____698 in
    FStar_ST.write scopes uu____692 in
  let mark1 uu____725 = push1 () in
  let reset_mark1 uu____729 = pop1 () in
  let commit_mark1 uu____733 =
    let uu____734 = FStar_ST.read scopes in
    match uu____734 with
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
    | uu____794 -> failwith "Impossible" in
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
    let uu___126_803 = x in
    let uu____804 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____804;
      FStar_Syntax_Syntax.index = (uu___126_803.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___126_803.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term option* FStar_SMTEncoding_Term.term option)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____827 -> false
let __proj__Binding_var__item___0:
  binding -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____851 -> false
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
         (fun uu___102_1039  ->
            match uu___102_1039 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1042 -> [])) in
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
    let uu____1050 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___103_1054  ->
              match uu___103_1054 with
              | Binding_var (x,uu____1056) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1058,uu____1059,uu____1060) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1050 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string option =
  fun env  ->
    fun t  ->
      let uu____1093 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1093
      then
        let uu____1095 = FStar_Syntax_Print.term_to_string t in
        Some uu____1095
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1106 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1106)
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
        (let uu___127_1118 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___127_1118.tcenv);
           warn = (uu___127_1118.warn);
           cache = (uu___127_1118.cache);
           nolabels = (uu___127_1118.nolabels);
           use_zfuel_name = (uu___127_1118.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___127_1118.encode_non_total_function_typ);
           current_module_name = (uu___127_1118.current_module_name)
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
        (let uu___128_1131 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___128_1131.depth);
           tcenv = (uu___128_1131.tcenv);
           warn = (uu___128_1131.warn);
           cache = (uu___128_1131.cache);
           nolabels = (uu___128_1131.nolabels);
           use_zfuel_name = (uu___128_1131.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_1131.encode_non_total_function_typ);
           current_module_name = (uu___128_1131.current_module_name)
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
          (let uu___129_1147 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___129_1147.depth);
             tcenv = (uu___129_1147.tcenv);
             warn = (uu___129_1147.warn);
             cache = (uu___129_1147.cache);
             nolabels = (uu___129_1147.nolabels);
             use_zfuel_name = (uu___129_1147.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___129_1147.encode_non_total_function_typ);
             current_module_name = (uu___129_1147.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___130_1157 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___130_1157.depth);
          tcenv = (uu___130_1157.tcenv);
          warn = (uu___130_1157.warn);
          cache = (uu___130_1157.cache);
          nolabels = (uu___130_1157.nolabels);
          use_zfuel_name = (uu___130_1157.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___130_1157.encode_non_total_function_typ);
          current_module_name = (uu___130_1157.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___104_1173  ->
             match uu___104_1173 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1181 -> None) in
      let uu____1184 = aux a in
      match uu____1184 with
      | None  ->
          let a2 = unmangle a in
          let uu____1191 = aux a2 in
          (match uu____1191 with
           | None  ->
               let uu____1197 =
                 let uu____1198 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1199 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1198 uu____1199 in
               failwith uu____1197
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1219 =
        let uu___131_1220 = env in
        let uu____1221 =
          let uu____1223 =
            let uu____1224 =
              let uu____1231 =
                let uu____1233 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_39  -> Some _0_39) uu____1233 in
              (x, fname, uu____1231, None) in
            Binding_fvar uu____1224 in
          uu____1223 :: (env.bindings) in
        {
          bindings = uu____1221;
          depth = (uu___131_1220.depth);
          tcenv = (uu___131_1220.tcenv);
          warn = (uu___131_1220.warn);
          cache = (uu___131_1220.cache);
          nolabels = (uu___131_1220.nolabels);
          use_zfuel_name = (uu___131_1220.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_1220.encode_non_total_function_typ);
          current_module_name = (uu___131_1220.current_module_name)
        } in
      (fname, ftok, uu____1219)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option) option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___105_1255  ->
           match uu___105_1255 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1277 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1289 =
        lookup_binding env
          (fun uu___106_1291  ->
             match uu___106_1291 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1301 -> None) in
      FStar_All.pipe_right uu____1289 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option)
  =
  fun env  ->
    fun a  ->
      let uu____1314 = try_lookup_lid env a in
      match uu____1314 with
      | None  ->
          let uu____1331 =
            let uu____1332 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1332 in
          failwith uu____1331
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
          let uu___132_1363 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___132_1363.depth);
            tcenv = (uu___132_1363.tcenv);
            warn = (uu___132_1363.warn);
            cache = (uu___132_1363.cache);
            nolabels = (uu___132_1363.nolabels);
            use_zfuel_name = (uu___132_1363.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___132_1363.encode_non_total_function_typ);
            current_module_name = (uu___132_1363.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1375 = lookup_lid env x in
        match uu____1375 with
        | (t1,t2,uu____1383) ->
            let t3 =
              let uu____1389 =
                let uu____1393 =
                  let uu____1395 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1395] in
                (f, uu____1393) in
              FStar_SMTEncoding_Util.mkApp uu____1389 in
            let uu___133_1398 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___133_1398.depth);
              tcenv = (uu___133_1398.tcenv);
              warn = (uu___133_1398.warn);
              cache = (uu___133_1398.cache);
              nolabels = (uu___133_1398.nolabels);
              use_zfuel_name = (uu___133_1398.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___133_1398.encode_non_total_function_typ);
              current_module_name = (uu___133_1398.current_module_name)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term option =
  fun env  ->
    fun l  ->
      let uu____1408 = try_lookup_lid env l in
      match uu____1408 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1435 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1440,fuel::[]) ->
                         let uu____1443 =
                           let uu____1444 =
                             let uu____1445 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1445
                               FStar_Pervasives.fst in
                           FStar_Util.starts_with uu____1444 "fuel" in
                         if uu____1443
                         then
                           let uu____1447 =
                             let uu____1448 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1448
                               fuel in
                           FStar_All.pipe_left (fun _0_40  -> Some _0_40)
                             uu____1447
                         else Some t
                     | uu____1451 -> Some t)
                | uu____1452 -> None))
let lookup_free_var env a =
  let uu____1470 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1470 with
  | Some t -> t
  | None  ->
      let uu____1473 =
        let uu____1474 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1474 in
      failwith uu____1473
let lookup_free_var_name env a =
  let uu____1491 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1491 with | (x,uu____1498,uu____1499) -> x
let lookup_free_var_sym env a =
  let uu____1523 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1523 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1544;
             FStar_SMTEncoding_Term.rng = uu____1545;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1553 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1567 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name: env_t -> Prims.string -> FStar_SMTEncoding_Term.term option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___107_1576  ->
           match uu___107_1576 with
           | Binding_fvar (uu____1578,nm',tok,uu____1581) when nm = nm' ->
               tok
           | uu____1586 -> None)
let mkForall_fuel' n1 uu____1603 =
  match uu____1603 with
  | (pats,vars,body) ->
      let fallback uu____1619 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1622 = FStar_Options.unthrottle_inductives () in
      if uu____1622
      then fallback ()
      else
        (let uu____1624 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1624 with
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
                       | uu____1643 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1657 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1657
                     | uu____1659 ->
                         let uu____1660 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1660 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1663 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____1689 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____1697 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____1702 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____1703 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____1712 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____1727 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1729 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1729 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____1743;
             FStar_Syntax_Syntax.pos = uu____1744;
             FStar_Syntax_Syntax.vars = uu____1745;_},uu____1746)
          ->
          let uu____1761 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1761 FStar_Option.isNone
      | uu____1774 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1781 =
        let uu____1782 = FStar_Syntax_Util.un_uinst t in
        uu____1782.FStar_Syntax_Syntax.n in
      match uu____1781 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1785,uu____1786,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___108_1815  ->
                  match uu___108_1815 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1816 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1817,uu____1818,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1845 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1845 FStar_Option.isSome
      | uu____1858 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1865 = head_normal env t in
      if uu____1865
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
    let uu____1876 =
      let uu____1877 = FStar_Syntax_Syntax.null_binder t in [uu____1877] in
    let uu____1878 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1876 uu____1878 None
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
                    let uu____1905 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1905
                | s ->
                    let uu____1908 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1908) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___109_1920  ->
    match uu___109_1920 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1921 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____1949;
                       FStar_SMTEncoding_Term.rng = uu____1950;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1964) ->
              let uu____1969 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1979 -> false) args (FStar_List.rev xs)) in
              if uu____1969 then tok_of_name env f else None
          | (uu____1982,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1985 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1987 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1987)) in
              if uu____1985 then Some t else None
          | uu____1990 -> None in
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
    | uu____2081 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___110_2084  ->
    match uu___110_2084 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2086 =
          let uu____2090 =
            let uu____2092 =
              let uu____2093 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2093 in
            [uu____2092] in
          ("FStar.Char.Char", uu____2090) in
        FStar_SMTEncoding_Util.mkApp uu____2086
    | FStar_Const.Const_int (i,None ) ->
        let uu____2101 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2101
    | FStar_Const.Const_int (i,Some uu____2103) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2112) ->
        let uu____2115 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2115
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2119 =
          let uu____2120 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2120 in
        failwith uu____2119
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2139 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2147 ->
            let uu____2152 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2152
        | uu____2153 ->
            if norm1
            then let uu____2154 = whnf env t1 in aux false uu____2154
            else
              (let uu____2156 =
                 let uu____2157 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2158 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2157 uu____2158 in
               failwith uu____2156) in
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
    | uu____2179 ->
        let uu____2180 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2180)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2208::uu____2209::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Syntax_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2212::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2214 -> false
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
        (let uu____2352 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2352
         then
           let uu____2353 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2353
         else ());
        (let uu____2355 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2391  ->
                   fun b  ->
                     match uu____2391 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2434 =
                           let x = unmangle (fst b) in
                           let uu____2443 = gen_term_var env1 x in
                           match uu____2443 with
                           | (xxsym,xx,env') ->
                               let uu____2457 =
                                 let uu____2460 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2460 env1 xx in
                               (match uu____2457 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2434 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2355 with
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
          let uu____2548 = encode_term t env in
          match uu____2548 with
          | (t1,decls) ->
              let uu____2555 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2555, decls)
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
          let uu____2563 = encode_term t env in
          match uu____2563 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2572 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2572, decls)
               | Some f ->
                   let uu____2574 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2574, decls))
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
        let uu____2580 = encode_args args_e env in
        match uu____2580 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2592 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____2599 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____2599 in
            let binary arg_tms1 =
              let uu____2608 =
                let uu____2609 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____2609 in
              let uu____2610 =
                let uu____2611 =
                  let uu____2612 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2612 in
                FStar_SMTEncoding_Term.unboxInt uu____2611 in
              (uu____2608, uu____2610) in
            let mk_default uu____2617 =
              let uu____2618 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2618 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____2663 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2663
              then
                let uu____2664 = let uu____2665 = mk_args ts in op uu____2665 in
                FStar_All.pipe_right uu____2664 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____2688 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____2688
              then
                let uu____2689 = binary ts in
                match uu____2689 with
                | (t1,t2) ->
                    let uu____2694 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____2694
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2697 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____2697
                 then
                   let uu____2698 = op (binary ts) in
                   FStar_All.pipe_right uu____2698
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
            let uu____2788 =
              let uu____2794 =
                FStar_List.tryFind
                  (fun uu____2806  ->
                     match uu____2806 with
                     | (l,uu____2813) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____2794 FStar_Util.must in
            (match uu____2788 with
             | (uu____2838,op) ->
                 let uu____2846 = op arg_tms in (uu____2846, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2853 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2853
       then
         let uu____2854 = FStar_Syntax_Print.tag_of_term t in
         let uu____2855 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2856 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2854 uu____2855
           uu____2856
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2860 ->
           let uu____2881 =
             let uu____2882 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2883 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2884 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2885 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2882
               uu____2883 uu____2884 uu____2885 in
           failwith uu____2881
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2888 =
             let uu____2889 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2890 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2891 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2892 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2889
               uu____2890 uu____2891 uu____2892 in
           failwith uu____2888
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2896 =
             let uu____2897 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2897 in
           failwith uu____2896
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2902) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2932) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2941 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2941, [])
       | FStar_Syntax_Syntax.Tm_type uu____2947 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2950) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2956 = encode_const c in (uu____2956, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2971 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2971 with
            | (binders1,res) ->
                let uu____2978 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2978
                then
                  let uu____2981 = encode_binders None binders1 env in
                  (match uu____2981 with
                   | (vars,guards,env',decls,uu____2996) ->
                       let fsym =
                         let uu____3006 = varops.fresh "f" in
                         (uu____3006, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____3009 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___134_3013 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___134_3013.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___134_3013.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___134_3013.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___134_3013.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___134_3013.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___134_3013.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___134_3013.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___134_3013.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___134_3013.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___134_3013.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___134_3013.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___134_3013.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___134_3013.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___134_3013.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___134_3013.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___134_3013.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___134_3013.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___134_3013.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___134_3013.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___134_3013.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___134_3013.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___134_3013.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___134_3013.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___134_3013.FStar_TypeChecker_Env.proof_ns)
                            }) res in
                       (match uu____3009 with
                        | (pre_opt,res_t) ->
                            let uu____3020 =
                              encode_term_pred None res_t env' app in
                            (match uu____3020 with
                             | (res_pred,decls') ->
                                 let uu____3027 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____3034 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____3034, [])
                                   | Some pre ->
                                       let uu____3037 =
                                         encode_formula pre env' in
                                       (match uu____3037 with
                                        | (guard,decls0) ->
                                            let uu____3045 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3045, decls0)) in
                                 (match uu____3027 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3053 =
                                          let uu____3059 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3059) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3053 in
                                      let cvars =
                                        let uu____3069 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3069
                                          (FStar_List.filter
                                             (fun uu____3075  ->
                                                match uu____3075 with
                                                | (x,uu____3079) ->
                                                    x <> (fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3090 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3090 with
                                       | Some cache_entry ->
                                           let uu____3095 =
                                             let uu____3096 =
                                               let uu____3100 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3100) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3096 in
                                           (uu____3095,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____3111 =
                                               let uu____3112 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3112 in
                                             varops.mk_unique uu____3111 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars in
                                           let caption =
                                             let uu____3119 =
                                               FStar_Options.log_queries () in
                                             if uu____3119
                                             then
                                               let uu____3121 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____3121
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3127 =
                                               let uu____3131 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3131) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3127 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3139 =
                                               let uu____3143 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3143, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3139 in
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
                                             let uu____3156 =
                                               let uu____3160 =
                                                 let uu____3161 =
                                                   let uu____3167 =
                                                     let uu____3168 =
                                                       let uu____3171 =
                                                         let uu____3172 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3172 in
                                                       (f_has_t, uu____3171) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3168 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3167) in
                                                 mkForall_fuel uu____3161 in
                                               (uu____3160,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3156 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3185 =
                                               let uu____3189 =
                                                 let uu____3190 =
                                                   let uu____3196 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3196) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3190 in
                                               (uu____3189, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3185 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3210 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3210);
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
                     let uu____3221 =
                       let uu____3225 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3225, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3221 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3234 =
                       let uu____3238 =
                         let uu____3239 =
                           let uu____3245 =
                             let uu____3246 =
                               let uu____3249 =
                                 let uu____3250 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3250 in
                               (f_has_t, uu____3249) in
                             FStar_SMTEncoding_Util.mkImp uu____3246 in
                           ([[f_has_t]], [fsym], uu____3245) in
                         mkForall_fuel uu____3239 in
                       (uu____3238, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3234 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3264 ->
           let uu____3269 =
             let uu____3272 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3272 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3277;
                 FStar_Syntax_Syntax.pos = uu____3278;
                 FStar_Syntax_Syntax.vars = uu____3279;_} ->
                 let uu____3286 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____3286 with
                  | (b,f1) ->
                      let uu____3300 =
                        let uu____3301 = FStar_List.hd b in fst uu____3301 in
                      (uu____3300, f1))
             | uu____3306 -> failwith "impossible" in
           (match uu____3269 with
            | (x,f) ->
                let uu____3313 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3313 with
                 | (base_t,decls) ->
                     let uu____3320 = gen_term_var env x in
                     (match uu____3320 with
                      | (x1,xtm,env') ->
                          let uu____3329 = encode_formula f env' in
                          (match uu____3329 with
                           | (refinement,decls') ->
                               let uu____3336 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3336 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3347 =
                                        let uu____3349 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3353 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3349
                                          uu____3353 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3347 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3369  ->
                                              match uu____3369 with
                                              | (y,uu____3373) ->
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
                                    let uu____3392 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3392 with
                                     | Some cache_entry ->
                                         let uu____3397 =
                                           let uu____3398 =
                                             let uu____3402 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3402) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3398 in
                                         (uu____3397,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3414 =
                                             let uu____3415 =
                                               let uu____3416 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3416 in
                                             Prims.strcat module_name
                                               uu____3415 in
                                           varops.mk_unique uu____3414 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3425 =
                                             let uu____3429 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3429) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3425 in
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
                                           let uu____3440 =
                                             let uu____3444 =
                                               let uu____3445 =
                                                 let uu____3451 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3451) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3445 in
                                             (uu____3444,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3440 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____3466 =
                                             let uu____3470 =
                                               let uu____3471 =
                                                 let uu____3477 =
                                                   let uu____3478 =
                                                     let uu____3481 =
                                                       let uu____3482 =
                                                         let uu____3488 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____3488) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____3482 in
                                                     (uu____3481, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____3478 in
                                                 ([[valid_t]], cvars1,
                                                   uu____3477) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3471 in
                                             (uu____3470,
                                               (Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3466 in
                                         let t_kinding =
                                           let uu____3508 =
                                             let uu____3512 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3512,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3508 in
                                         let t_interp =
                                           let uu____3522 =
                                             let uu____3526 =
                                               let uu____3527 =
                                                 let uu____3533 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3533) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3527 in
                                             let uu____3545 =
                                               let uu____3547 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3547 in
                                             (uu____3526, uu____3545,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3522 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3552 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3552);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3569 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3569 in
           let uu____3570 = encode_term_pred None k env ttm in
           (match uu____3570 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3578 =
                    let uu____3582 =
                      let uu____3583 =
                        let uu____3584 =
                          let uu____3585 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3585 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3584 in
                      varops.mk_unique uu____3583 in
                    (t_has_k, (Some "Uvar typing"), uu____3582) in
                  FStar_SMTEncoding_Util.mkAssume uu____3578 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3588 ->
           let uu____3598 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3598 with
            | (head1,args_e) ->
                let uu____3626 =
                  let uu____3634 =
                    let uu____3635 = FStar_Syntax_Subst.compress head1 in
                    uu____3635.FStar_Syntax_Syntax.n in
                  (uu____3634, args_e) in
                (match uu____3626 with
                 | uu____3645 when head_redex env head1 ->
                     let uu____3653 = whnf env t in
                     encode_term uu____3653 env
                 | uu____3654 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____3667;
                       FStar_Syntax_Syntax.pos = uu____3668;
                       FStar_Syntax_Syntax.vars = uu____3669;_},uu____3670),uu____3671::
                    (v1,uu____3673)::(v2,uu____3675)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3713 = encode_term v1 env in
                     (match uu____3713 with
                      | (v11,decls1) ->
                          let uu____3720 = encode_term v2 env in
                          (match uu____3720 with
                           | (v21,decls2) ->
                               let uu____3727 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3727,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3730::(v1,uu____3732)::(v2,uu____3734)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3768 = encode_term v1 env in
                     (match uu____3768 with
                      | (v11,decls1) ->
                          let uu____3775 = encode_term v2 env in
                          (match uu____3775 with
                           | (v21,decls2) ->
                               let uu____3782 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3782,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3784) ->
                     let e0 =
                       let uu____3796 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3796 in
                     ((let uu____3802 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3802
                       then
                         let uu____3803 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3803
                       else ());
                      (let e =
                         let uu____3808 =
                           let uu____3809 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3810 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3809
                             uu____3810 in
                         uu____3808 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3819),(arg,uu____3821)::[]) -> encode_term arg env
                 | uu____3839 ->
                     let uu____3847 = encode_args args_e env in
                     (match uu____3847 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3880 = encode_term head1 env in
                            match uu____3880 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3919 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3919 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3961  ->
                                                 fun uu____3962  ->
                                                   match (uu____3961,
                                                           uu____3962)
                                                   with
                                                   | ((bv,uu____3976),
                                                      (a,uu____3978)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3992 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3992
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3997 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3997 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____4007 =
                                                   let uu____4011 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____4016 =
                                                     let uu____4017 =
                                                       let uu____4018 =
                                                         let uu____4019 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____4019 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____4018 in
                                                     varops.mk_unique
                                                       uu____4017 in
                                                   (uu____4011,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____4016) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____4007 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____4036 = lookup_free_var_sym env fv in
                            match uu____4036 with
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
                                   FStar_Syntax_Syntax.tk = uu____4059;
                                   FStar_Syntax_Syntax.pos = uu____4060;
                                   FStar_Syntax_Syntax.vars = uu____4061;_},uu____4062)
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____4073;
                                   FStar_Syntax_Syntax.pos = uu____4074;
                                   FStar_Syntax_Syntax.vars = uu____4075;_},uu____4076)
                                ->
                                let uu____4081 =
                                  let uu____4082 =
                                    let uu____4085 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4085
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4082
                                    FStar_Pervasives.snd in
                                Some uu____4081
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4105 =
                                  let uu____4106 =
                                    let uu____4109 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4109
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4106
                                    FStar_Pervasives.snd in
                                Some uu____4105
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4128,(FStar_Util.Inl t1,uu____4130),uu____4131)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4169,(FStar_Util.Inr c,uu____4171),uu____4172)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4210 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4230 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4230 in
                               let uu____4231 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4231 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4241;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4242;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4243;_},uu____4244)
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
                                     | uu____4268 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4313 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4313 with
            | (bs1,body1,opening) ->
                let fallback uu____4328 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____4333 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4333, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4344 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____4344
                  | FStar_Util.Inr (eff,uu____4346) ->
                      let uu____4352 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____4352 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4397 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___135_4398 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___135_4398.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___135_4398.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___135_4398.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___135_4398.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___135_4398.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___135_4398.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___135_4398.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___135_4398.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___135_4398.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___135_4398.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___135_4398.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___135_4398.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___135_4398.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___135_4398.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___135_4398.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___135_4398.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___135_4398.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___135_4398.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___135_4398.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___135_4398.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___135_4398.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___135_4398.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___135_4398.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___135_4398.FStar_TypeChecker_Env.proof_ns)
                             }) uu____4397 FStar_Syntax_Syntax.U_unknown in
                        let uu____4399 =
                          let uu____4400 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4400 in
                        FStar_Util.Inl uu____4399
                    | FStar_Util.Inr (eff_name,uu____4407) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4438 =
                        let uu____4439 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4439 in
                      FStar_All.pipe_right uu____4438
                        (fun _0_41  -> Some _0_41)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4451 =
                        let uu____4452 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4452 FStar_Pervasives.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4460 =
                          let uu____4461 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4461 in
                        FStar_All.pipe_right uu____4460
                          (fun _0_42  -> Some _0_42)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4465 =
                             let uu____4466 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4466 in
                           FStar_All.pipe_right uu____4465
                             (fun _0_43  -> Some _0_43))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4477 =
                         let uu____4478 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4478 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4477);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4493 =
                       (is_impure lc1) &&
                         (let uu____4494 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4494) in
                     if uu____4493
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4499 = encode_binders None bs1 env in
                        match uu____4499 with
                        | (vars,guards,envbody,decls,uu____4514) ->
                            let uu____4521 =
                              let uu____4529 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4529
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4521 with
                             | (lc2,body2) ->
                                 let uu____4554 = encode_term body2 envbody in
                                 (match uu____4554 with
                                  | (body3,decls') ->
                                      let uu____4561 =
                                        let uu____4566 = codomain_eff lc2 in
                                        match uu____4566 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4578 =
                                              encode_term tfun env in
                                            (match uu____4578 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4561 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4597 =
                                               let uu____4603 =
                                                 let uu____4604 =
                                                   let uu____4607 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4607, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4604 in
                                               ([], vars, uu____4603) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4597 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4615 =
                                                   let uu____4617 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4617 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4615 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4628 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4628 with
                                            | Some cache_entry ->
                                                let uu____4633 =
                                                  let uu____4634 =
                                                    let uu____4638 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4638) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4634 in
                                                (uu____4633,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | None  ->
                                                let uu____4644 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4644 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4651 =
                                                         let uu____4652 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4652 =
                                                           cache_size in
                                                       if uu____4651
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
                                                         let uu____4663 =
                                                           let uu____4664 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4664 in
                                                         varops.mk_unique
                                                           uu____4663 in
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
                                                       let uu____4669 =
                                                         let uu____4673 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4673) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4669 in
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
                                                           let uu____4685 =
                                                             let uu____4686 =
                                                               let uu____4690
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4690,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4686 in
                                                           [uu____4685] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4698 =
                                                         let uu____4702 =
                                                           let uu____4703 =
                                                             let uu____4709 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4709) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4703 in
                                                         (uu____4702,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4698 in
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
                                                     ((let uu____4719 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4719);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4721,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4722;
                          FStar_Syntax_Syntax.lbunivs = uu____4723;
                          FStar_Syntax_Syntax.lbtyp = uu____4724;
                          FStar_Syntax_Syntax.lbeff = uu____4725;
                          FStar_Syntax_Syntax.lbdef = uu____4726;_}::uu____4727),uu____4728)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4746;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4748;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4764 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4777 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4777, [decl_e])))
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
              let uu____4819 = encode_term e1 env in
              match uu____4819 with
              | (ee1,decls1) ->
                  let uu____4826 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4826 with
                   | (xs,e21) ->
                       let uu____4840 = FStar_List.hd xs in
                       (match uu____4840 with
                        | (x1,uu____4848) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4850 = encode_body e21 env' in
                            (match uu____4850 with
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
            let uu____4872 =
              let uu____4876 =
                let uu____4877 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4877 in
              gen_term_var env uu____4876 in
            match uu____4872 with
            | (scrsym,scr',env1) ->
                let uu____4887 = encode_term e env1 in
                (match uu____4887 with
                 | (scr,decls) ->
                     let uu____4894 =
                       let encode_branch b uu____4910 =
                         match uu____4910 with
                         | (else_case,decls1) ->
                             let uu____4921 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4921 with
                              | (p,w,br) ->
                                  let uu____4942 = encode_pat env1 p in
                                  (match uu____4942 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____4962  ->
                                                   match uu____4962 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____4967 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____4982 =
                                               encode_term w1 env2 in
                                             (match uu____4982 with
                                              | (w2,decls2) ->
                                                  let uu____4990 =
                                                    let uu____4991 =
                                                      let uu____4994 =
                                                        let uu____4995 =
                                                          let uu____4998 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____4998) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____4995 in
                                                      (guard, uu____4994) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____4991 in
                                                  (uu____4990, decls2)) in
                                       (match uu____4967 with
                                        | (guard1,decls2) ->
                                            let uu____5006 =
                                              encode_br br env2 in
                                            (match uu____5006 with
                                             | (br1,decls3) ->
                                                 let uu____5014 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____5014,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4894 with
                      | (match_tm,decls1) ->
                          let uu____5025 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____5025, decls1)))
and encode_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____5047 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5047
       then
         let uu____5048 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5048
       else ());
      (let uu____5050 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5050 with
       | (vars,pat_term) ->
           let uu____5060 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5083  ->
                     fun v1  ->
                       match uu____5083 with
                       | (env1,vars1) ->
                           let uu____5111 = gen_term_var env1 v1 in
                           (match uu____5111 with
                            | (xx,uu____5123,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____5060 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5170 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5171 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5172 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5178 =
                        let uu____5181 = encode_const c in
                        (scrutinee, uu____5181) in
                      FStar_SMTEncoding_Util.mkEq uu____5178
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5200 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5200 with
                        | (uu____5204,uu____5205::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5207 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5228  ->
                                  match uu____5228 with
                                  | (arg,uu____5234) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5244 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5244)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5264) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5283 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5298 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5320  ->
                                  match uu____5320 with
                                  | (arg,uu____5329) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5339 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5339)) in
                      FStar_All.pipe_right uu____5298 FStar_List.flatten in
                let pat_term1 uu____5355 = encode_term pat_term env1 in
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
      let uu____5362 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5377  ->
                fun uu____5378  ->
                  match (uu____5377, uu____5378) with
                  | ((tms,decls),(t,uu____5398)) ->
                      let uu____5409 = encode_term t env in
                      (match uu____5409 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5362 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5443 = FStar_Syntax_Util.list_elements e in
        match uu____5443 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5461 =
          let uu____5471 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5471 FStar_Syntax_Util.head_and_args in
        match uu____5461 with
        | (head1,args) ->
            let uu____5502 =
              let uu____5510 =
                let uu____5511 = FStar_Syntax_Util.un_uinst head1 in
                uu____5511.FStar_Syntax_Syntax.n in
              (uu____5510, args) in
            (match uu____5502 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5525,uu____5526)::(e,uu____5528)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> (e, None)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5559)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpatT_lid
                 -> (e, None)
             | uu____5580 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or t1 =
          let uu____5613 =
            let uu____5623 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5623 FStar_Syntax_Util.head_and_args in
          match uu____5613 with
          | (head1,args) ->
              let uu____5652 =
                let uu____5660 =
                  let uu____5661 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5661.FStar_Syntax_Syntax.n in
                (uu____5660, args) in
              (match uu____5652 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5674)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5694 -> None) in
        match elts with
        | t1::[] ->
            let uu____5712 = smt_pat_or t1 in
            (match uu____5712 with
             | Some e ->
                 let uu____5728 = list_elements1 e in
                 FStar_All.pipe_right uu____5728
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5745 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5745
                           (FStar_List.map one_pat)))
             | uu____5759 ->
                 let uu____5763 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5763])
        | uu____5794 ->
            let uu____5796 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5796] in
      let uu____5827 =
        let uu____5843 =
          let uu____5844 = FStar_Syntax_Subst.compress t in
          uu____5844.FStar_Syntax_Syntax.n in
        match uu____5843 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5874 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5874 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5909;
                        FStar_Syntax_Syntax.effect_name = uu____5910;
                        FStar_Syntax_Syntax.result_typ = uu____5911;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5913)::(post,uu____5915)::(pats,uu____5917)::[];
                        FStar_Syntax_Syntax.flags = uu____5918;_}
                      ->
                      let uu____5950 = lemma_pats pats in
                      (binders1, pre, post, uu____5950)
                  | uu____5969 -> failwith "impos"))
        | uu____5985 -> failwith "Impos" in
      match uu____5827 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___136_6030 = env in
            {
              bindings = (uu___136_6030.bindings);
              depth = (uu___136_6030.depth);
              tcenv = (uu___136_6030.tcenv);
              warn = (uu___136_6030.warn);
              cache = (uu___136_6030.cache);
              nolabels = (uu___136_6030.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___136_6030.encode_non_total_function_typ);
              current_module_name = (uu___136_6030.current_module_name)
            } in
          let uu____6031 = encode_binders None binders env1 in
          (match uu____6031 with
           | (vars,guards,env2,decls,uu____6046) ->
               let uu____6053 =
                 let uu____6060 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____6091 =
                             let uu____6096 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun uu____6112  ->
                                       match uu____6112 with
                                       | (t1,uu____6119) ->
                                           encode_term t1 env2)) in
                             FStar_All.pipe_right uu____6096 FStar_List.unzip in
                           match uu____6091 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____6060 FStar_List.unzip in
               (match uu____6053 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___137_6169 = env2 in
                      {
                        bindings = (uu___137_6169.bindings);
                        depth = (uu___137_6169.depth);
                        tcenv = (uu___137_6169.tcenv);
                        warn = (uu___137_6169.warn);
                        cache = (uu___137_6169.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___137_6169.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___137_6169.encode_non_total_function_typ);
                        current_module_name =
                          (uu___137_6169.current_module_name)
                      } in
                    let uu____6170 =
                      let uu____6173 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6173 env3 in
                    (match uu____6170 with
                     | (pre1,decls'') ->
                         let uu____6178 =
                           let uu____6181 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6181 env3 in
                         (match uu____6178 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6188 =
                                let uu____6189 =
                                  let uu____6195 =
                                    let uu____6196 =
                                      let uu____6199 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6199, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6196 in
                                  (pats, vars, uu____6195) in
                                FStar_SMTEncoding_Util.mkForall uu____6189 in
                              (uu____6188, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6212 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6212
        then
          let uu____6213 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6214 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6213 uu____6214
        else () in
      let enc f r l =
        let uu____6241 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6254 = encode_term (fst x) env in
                 match uu____6254 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6241 with
        | (decls,args) ->
            let uu____6271 =
              let uu___138_6272 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___138_6272.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___138_6272.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6271, decls) in
      let const_op f r uu____6297 = let uu____6306 = f r in (uu____6306, []) in
      let un_op f l =
        let uu____6322 = FStar_List.hd l in FStar_All.pipe_left f uu____6322 in
      let bin_op f uu___111_6335 =
        match uu___111_6335 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6343 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6370 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6379  ->
                 match uu____6379 with
                 | (t,uu____6387) ->
                     let uu____6388 = encode_formula t env in
                     (match uu____6388 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6370 with
        | (decls,phis) ->
            let uu____6405 =
              let uu___139_6406 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6406.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6406.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6405, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____6445  ->
               match uu____6445 with
               | (a,q) ->
                   (match q with
                    | Some (FStar_Syntax_Syntax.Implicit uu____6459) -> false
                    | uu____6460 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____6471 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____6471
        else
          (let uu____6483 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____6483 r rf) in
      let mk_imp1 r uu___112_6502 =
        match uu___112_6502 with
        | (lhs,uu____6506)::(rhs,uu____6508)::[] ->
            let uu____6529 = encode_formula rhs env in
            (match uu____6529 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6538) ->
                      (l1, decls1)
                  | uu____6541 ->
                      let uu____6542 = encode_formula lhs env in
                      (match uu____6542 with
                       | (l2,decls2) ->
                           let uu____6549 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6549, (FStar_List.append decls1 decls2)))))
        | uu____6551 -> failwith "impossible" in
      let mk_ite r uu___113_6566 =
        match uu___113_6566 with
        | (guard,uu____6570)::(_then,uu____6572)::(_else,uu____6574)::[] ->
            let uu____6603 = encode_formula guard env in
            (match uu____6603 with
             | (g,decls1) ->
                 let uu____6610 = encode_formula _then env in
                 (match uu____6610 with
                  | (t,decls2) ->
                      let uu____6617 = encode_formula _else env in
                      (match uu____6617 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6626 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6645 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6645 in
      let connectives =
        let uu____6657 =
          let uu____6666 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6666) in
        let uu____6679 =
          let uu____6689 =
            let uu____6698 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6698) in
          let uu____6711 =
            let uu____6721 =
              let uu____6731 =
                let uu____6740 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6740) in
              let uu____6753 =
                let uu____6763 =
                  let uu____6773 =
                    let uu____6782 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6782) in
                  [uu____6773;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6763 in
              uu____6731 :: uu____6753 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6721 in
          uu____6689 :: uu____6711 in
        uu____6657 :: uu____6679 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6998 = encode_formula phi' env in
            (match uu____6998 with
             | (phi2,decls) ->
                 let uu____7005 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____7005, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____7006 ->
            let uu____7011 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____7011 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____7040 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____7040 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____7048;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____7050;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____7066 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____7066 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____7098::(x,uu____7100)::(t,uu____7102)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____7136 = encode_term x env in
                 (match uu____7136 with
                  | (x1,decls) ->
                      let uu____7143 = encode_term t env in
                      (match uu____7143 with
                       | (t1,decls') ->
                           let uu____7150 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____7150, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____7154)::(msg,uu____7156)::(phi2,uu____7158)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____7192 =
                   let uu____7195 =
                     let uu____7196 = FStar_Syntax_Subst.compress r in
                     uu____7196.FStar_Syntax_Syntax.n in
                   let uu____7199 =
                     let uu____7200 = FStar_Syntax_Subst.compress msg in
                     uu____7200.FStar_Syntax_Syntax.n in
                   (uu____7195, uu____7199) in
                 (match uu____7192 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7207))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____7223 -> fallback phi2)
             | uu____7226 when head_redex env head2 ->
                 let uu____7234 = whnf env phi1 in
                 encode_formula uu____7234 env
             | uu____7235 ->
                 let uu____7243 = encode_term phi1 env in
                 (match uu____7243 with
                  | (tt,decls) ->
                      let uu____7250 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___140_7251 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___140_7251.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___140_7251.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7250, decls)))
        | uu____7254 ->
            let uu____7255 = encode_term phi1 env in
            (match uu____7255 with
             | (tt,decls) ->
                 let uu____7262 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___141_7263 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___141_7263.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___141_7263.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7262, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7290 = encode_binders None bs env1 in
        match uu____7290 with
        | (vars,guards,env2,decls,uu____7312) ->
            let uu____7319 =
              let uu____7326 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7349 =
                          let uu____7354 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7368  ->
                                    match uu____7368 with
                                    | (t,uu____7374) ->
                                        encode_term t
                                          (let uu___142_7375 = env2 in
                                           {
                                             bindings =
                                               (uu___142_7375.bindings);
                                             depth = (uu___142_7375.depth);
                                             tcenv = (uu___142_7375.tcenv);
                                             warn = (uu___142_7375.warn);
                                             cache = (uu___142_7375.cache);
                                             nolabels =
                                               (uu___142_7375.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___142_7375.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___142_7375.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7354 FStar_List.unzip in
                        match uu____7349 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7326 FStar_List.unzip in
            (match uu____7319 with
             | (pats,decls') ->
                 let uu____7427 = encode_formula body env2 in
                 (match uu____7427 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7446;
                             FStar_SMTEncoding_Term.rng = uu____7447;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7455 -> guards in
                      let uu____7458 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7458, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7492  ->
                   match uu____7492 with
                   | (x,uu____7496) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7502 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7508 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7508) uu____7502 tl1 in
             let uu____7510 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7522  ->
                       match uu____7522 with
                       | (b,uu____7526) ->
                           let uu____7527 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7527)) in
             (match uu____7510 with
              | None  -> ()
              | Some (x,uu____7531) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7541 =
                    let uu____7542 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7542 in
                  FStar_Errors.warn pos uu____7541) in
       let uu____7543 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7543 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7549 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7585  ->
                     match uu____7585 with
                     | (l,uu____7595) -> FStar_Ident.lid_equals op l)) in
           (match uu____7549 with
            | None  -> fallback phi1
            | Some (uu____7618,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7647 = encode_q_body env vars pats body in
             match uu____7647 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7673 =
                     let uu____7679 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7679) in
                   FStar_SMTEncoding_Term.mkForall uu____7673
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7691 = encode_q_body env vars pats body in
             match uu____7691 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7716 =
                   let uu____7717 =
                     let uu____7723 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7723) in
                   FStar_SMTEncoding_Term.mkExists uu____7717
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7716, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7777 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7777 with
  | (asym,a) ->
      let uu____7782 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7782 with
       | (xsym,x) ->
           let uu____7787 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7787 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7817 =
                      let uu____7823 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____7823, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7817 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7838 =
                      let uu____7842 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7842) in
                    FStar_SMTEncoding_Util.mkApp uu____7838 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7850 =
                    let uu____7852 =
                      let uu____7854 =
                        let uu____7856 =
                          let uu____7857 =
                            let uu____7861 =
                              let uu____7862 =
                                let uu____7868 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7868) in
                              FStar_SMTEncoding_Util.mkForall uu____7862 in
                            (uu____7861, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7857 in
                        let uu____7877 =
                          let uu____7879 =
                            let uu____7880 =
                              let uu____7884 =
                                let uu____7885 =
                                  let uu____7891 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7891) in
                                FStar_SMTEncoding_Util.mkForall uu____7885 in
                              (uu____7884,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7880 in
                          [uu____7879] in
                        uu____7856 :: uu____7877 in
                      xtok_decl :: uu____7854 in
                    xname_decl :: uu____7852 in
                  (xtok1, uu____7850) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7940 =
                    let uu____7948 =
                      let uu____7954 =
                        let uu____7955 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7955 in
                      quant axy uu____7954 in
                    (FStar_Syntax_Const.op_Eq, uu____7948) in
                  let uu____7961 =
                    let uu____7970 =
                      let uu____7978 =
                        let uu____7984 =
                          let uu____7985 =
                            let uu____7986 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7986 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7985 in
                        quant axy uu____7984 in
                      (FStar_Syntax_Const.op_notEq, uu____7978) in
                    let uu____7992 =
                      let uu____8001 =
                        let uu____8009 =
                          let uu____8015 =
                            let uu____8016 =
                              let uu____8017 =
                                let uu____8020 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8021 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____8020, uu____8021) in
                              FStar_SMTEncoding_Util.mkLT uu____8017 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____8016 in
                          quant xy uu____8015 in
                        (FStar_Syntax_Const.op_LT, uu____8009) in
                      let uu____8027 =
                        let uu____8036 =
                          let uu____8044 =
                            let uu____8050 =
                              let uu____8051 =
                                let uu____8052 =
                                  let uu____8055 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____8056 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____8055, uu____8056) in
                                FStar_SMTEncoding_Util.mkLTE uu____8052 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____8051 in
                            quant xy uu____8050 in
                          (FStar_Syntax_Const.op_LTE, uu____8044) in
                        let uu____8062 =
                          let uu____8071 =
                            let uu____8079 =
                              let uu____8085 =
                                let uu____8086 =
                                  let uu____8087 =
                                    let uu____8090 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____8091 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____8090, uu____8091) in
                                  FStar_SMTEncoding_Util.mkGT uu____8087 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____8086 in
                              quant xy uu____8085 in
                            (FStar_Syntax_Const.op_GT, uu____8079) in
                          let uu____8097 =
                            let uu____8106 =
                              let uu____8114 =
                                let uu____8120 =
                                  let uu____8121 =
                                    let uu____8122 =
                                      let uu____8125 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____8126 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____8125, uu____8126) in
                                    FStar_SMTEncoding_Util.mkGTE uu____8122 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____8121 in
                                quant xy uu____8120 in
                              (FStar_Syntax_Const.op_GTE, uu____8114) in
                            let uu____8132 =
                              let uu____8141 =
                                let uu____8149 =
                                  let uu____8155 =
                                    let uu____8156 =
                                      let uu____8157 =
                                        let uu____8160 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____8161 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____8160, uu____8161) in
                                      FStar_SMTEncoding_Util.mkSub uu____8157 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8156 in
                                  quant xy uu____8155 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____8149) in
                              let uu____8167 =
                                let uu____8176 =
                                  let uu____8184 =
                                    let uu____8190 =
                                      let uu____8191 =
                                        let uu____8192 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8192 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8191 in
                                    quant qx uu____8190 in
                                  (FStar_Syntax_Const.op_Minus, uu____8184) in
                                let uu____8198 =
                                  let uu____8207 =
                                    let uu____8215 =
                                      let uu____8221 =
                                        let uu____8222 =
                                          let uu____8223 =
                                            let uu____8226 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8227 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8226, uu____8227) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8223 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8222 in
                                      quant xy uu____8221 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8215) in
                                  let uu____8233 =
                                    let uu____8242 =
                                      let uu____8250 =
                                        let uu____8256 =
                                          let uu____8257 =
                                            let uu____8258 =
                                              let uu____8261 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8262 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8261, uu____8262) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8258 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8257 in
                                        quant xy uu____8256 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8250) in
                                    let uu____8268 =
                                      let uu____8277 =
                                        let uu____8285 =
                                          let uu____8291 =
                                            let uu____8292 =
                                              let uu____8293 =
                                                let uu____8296 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8297 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8296, uu____8297) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8293 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8292 in
                                          quant xy uu____8291 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8285) in
                                      let uu____8303 =
                                        let uu____8312 =
                                          let uu____8320 =
                                            let uu____8326 =
                                              let uu____8327 =
                                                let uu____8328 =
                                                  let uu____8331 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8332 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8331, uu____8332) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8328 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8327 in
                                            quant xy uu____8326 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8320) in
                                        let uu____8338 =
                                          let uu____8347 =
                                            let uu____8355 =
                                              let uu____8361 =
                                                let uu____8362 =
                                                  let uu____8363 =
                                                    let uu____8366 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8367 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8366, uu____8367) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8363 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8362 in
                                              quant xy uu____8361 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8355) in
                                          let uu____8373 =
                                            let uu____8382 =
                                              let uu____8390 =
                                                let uu____8396 =
                                                  let uu____8397 =
                                                    let uu____8398 =
                                                      let uu____8401 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8402 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8401,
                                                        uu____8402) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8398 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8397 in
                                                quant xy uu____8396 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8390) in
                                            let uu____8408 =
                                              let uu____8417 =
                                                let uu____8425 =
                                                  let uu____8431 =
                                                    let uu____8432 =
                                                      let uu____8433 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8433 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8432 in
                                                  quant qx uu____8431 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8425) in
                                              [uu____8417] in
                                            uu____8382 :: uu____8408 in
                                          uu____8347 :: uu____8373 in
                                        uu____8312 :: uu____8338 in
                                      uu____8277 :: uu____8303 in
                                    uu____8242 :: uu____8268 in
                                  uu____8207 :: uu____8233 in
                                uu____8176 :: uu____8198 in
                              uu____8141 :: uu____8167 in
                            uu____8106 :: uu____8132 in
                          uu____8071 :: uu____8097 in
                        uu____8036 :: uu____8062 in
                      uu____8001 :: uu____8027 in
                    uu____7970 :: uu____7992 in
                  uu____7940 :: uu____7961 in
                let mk1 l v1 =
                  let uu____8561 =
                    let uu____8566 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8598  ->
                              match uu____8598 with
                              | (l',uu____8607) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8566
                      (FStar_Option.map
                         (fun uu____8640  ->
                            match uu____8640 with | (uu____8651,b) -> b v1)) in
                  FStar_All.pipe_right uu____8561 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8692  ->
                          match uu____8692 with
                          | (l',uu____8701) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8727 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8727 with
        | (xxsym,xx) ->
            let uu____8732 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8732 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8740 =
                   let uu____8744 =
                     let uu____8745 =
                       let uu____8751 =
                         let uu____8752 =
                           let uu____8755 =
                             let uu____8756 =
                               let uu____8759 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8759) in
                             FStar_SMTEncoding_Util.mkEq uu____8756 in
                           (xx_has_type, uu____8755) in
                         FStar_SMTEncoding_Util.mkImp uu____8752 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8751) in
                     FStar_SMTEncoding_Util.mkForall uu____8745 in
                   let uu____8772 =
                     let uu____8773 =
                       let uu____8774 =
                         let uu____8775 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8775 in
                       Prims.strcat module_name uu____8774 in
                     varops.mk_unique uu____8773 in
                   (uu____8744, (Some "pretyping"), uu____8772) in
                 FStar_SMTEncoding_Util.mkAssume uu____8740)
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
    let uu____8805 =
      let uu____8806 =
        let uu____8810 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8810, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8806 in
    let uu____8812 =
      let uu____8814 =
        let uu____8815 =
          let uu____8819 =
            let uu____8820 =
              let uu____8826 =
                let uu____8827 =
                  let uu____8830 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8830) in
                FStar_SMTEncoding_Util.mkImp uu____8827 in
              ([[typing_pred]], [xx], uu____8826) in
            mkForall_fuel uu____8820 in
          (uu____8819, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8815 in
      [uu____8814] in
    uu____8805 :: uu____8812 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8858 =
      let uu____8859 =
        let uu____8863 =
          let uu____8864 =
            let uu____8870 =
              let uu____8873 =
                let uu____8875 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8875] in
              [uu____8873] in
            let uu____8878 =
              let uu____8879 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8879 tt in
            (uu____8870, [bb], uu____8878) in
          FStar_SMTEncoding_Util.mkForall uu____8864 in
        (uu____8863, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8859 in
    let uu____8890 =
      let uu____8892 =
        let uu____8893 =
          let uu____8897 =
            let uu____8898 =
              let uu____8904 =
                let uu____8905 =
                  let uu____8908 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8908) in
                FStar_SMTEncoding_Util.mkImp uu____8905 in
              ([[typing_pred]], [xx], uu____8904) in
            mkForall_fuel uu____8898 in
          (uu____8897, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8893 in
      [uu____8892] in
    uu____8858 :: uu____8890 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8942 =
        let uu____8943 =
          let uu____8947 =
            let uu____8949 =
              let uu____8951 =
                let uu____8953 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8954 =
                  let uu____8956 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8956] in
                uu____8953 :: uu____8954 in
              tt :: uu____8951 in
            tt :: uu____8949 in
          ("Prims.Precedes", uu____8947) in
        FStar_SMTEncoding_Util.mkApp uu____8943 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8942 in
    let precedes_y_x =
      let uu____8959 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8959 in
    let uu____8961 =
      let uu____8962 =
        let uu____8966 =
          let uu____8967 =
            let uu____8973 =
              let uu____8976 =
                let uu____8978 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8978] in
              [uu____8976] in
            let uu____8981 =
              let uu____8982 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8982 tt in
            (uu____8973, [bb], uu____8981) in
          FStar_SMTEncoding_Util.mkForall uu____8967 in
        (uu____8966, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8962 in
    let uu____8993 =
      let uu____8995 =
        let uu____8996 =
          let uu____9000 =
            let uu____9001 =
              let uu____9007 =
                let uu____9008 =
                  let uu____9011 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____9011) in
                FStar_SMTEncoding_Util.mkImp uu____9008 in
              ([[typing_pred]], [xx], uu____9007) in
            mkForall_fuel uu____9001 in
          (uu____9000, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8996 in
      let uu____9024 =
        let uu____9026 =
          let uu____9027 =
            let uu____9031 =
              let uu____9032 =
                let uu____9038 =
                  let uu____9039 =
                    let uu____9042 =
                      let uu____9043 =
                        let uu____9045 =
                          let uu____9047 =
                            let uu____9049 =
                              let uu____9050 =
                                let uu____9053 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____9054 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____9053, uu____9054) in
                              FStar_SMTEncoding_Util.mkGT uu____9050 in
                            let uu____9055 =
                              let uu____9057 =
                                let uu____9058 =
                                  let uu____9061 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____9062 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____9061, uu____9062) in
                                FStar_SMTEncoding_Util.mkGTE uu____9058 in
                              let uu____9063 =
                                let uu____9065 =
                                  let uu____9066 =
                                    let uu____9069 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____9070 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____9069, uu____9070) in
                                  FStar_SMTEncoding_Util.mkLT uu____9066 in
                                [uu____9065] in
                              uu____9057 :: uu____9063 in
                            uu____9049 :: uu____9055 in
                          typing_pred_y :: uu____9047 in
                        typing_pred :: uu____9045 in
                      FStar_SMTEncoding_Util.mk_and_l uu____9043 in
                    (uu____9042, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____9039 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____9038) in
              mkForall_fuel uu____9032 in
            (uu____9031, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____9027 in
        [uu____9026] in
      uu____8995 :: uu____9024 in
    uu____8961 :: uu____8993 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9100 =
      let uu____9101 =
        let uu____9105 =
          let uu____9106 =
            let uu____9112 =
              let uu____9115 =
                let uu____9117 = FStar_SMTEncoding_Term.boxString b in
                [uu____9117] in
              [uu____9115] in
            let uu____9120 =
              let uu____9121 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____9121 tt in
            (uu____9112, [bb], uu____9120) in
          FStar_SMTEncoding_Util.mkForall uu____9106 in
        (uu____9105, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9101 in
    let uu____9132 =
      let uu____9134 =
        let uu____9135 =
          let uu____9139 =
            let uu____9140 =
              let uu____9146 =
                let uu____9147 =
                  let uu____9150 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____9150) in
                FStar_SMTEncoding_Util.mkImp uu____9147 in
              ([[typing_pred]], [xx], uu____9146) in
            mkForall_fuel uu____9140 in
          (uu____9139, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9135 in
      [uu____9134] in
    uu____9100 :: uu____9132 in
  let mk_ref1 env reft_name uu____9172 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____9183 =
        let uu____9187 =
          let uu____9189 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9189] in
        (reft_name, uu____9187) in
      FStar_SMTEncoding_Util.mkApp uu____9183 in
    let refb =
      let uu____9192 =
        let uu____9196 =
          let uu____9198 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9198] in
        (reft_name, uu____9196) in
      FStar_SMTEncoding_Util.mkApp uu____9192 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9202 =
      let uu____9203 =
        let uu____9207 =
          let uu____9208 =
            let uu____9214 =
              let uu____9215 =
                let uu____9218 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9218) in
              FStar_SMTEncoding_Util.mkImp uu____9215 in
            ([[typing_pred]], [xx; aa], uu____9214) in
          mkForall_fuel uu____9208 in
        (uu____9207, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9203 in
    [uu____9202] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9258 =
      let uu____9259 =
        let uu____9263 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9263, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9259 in
    [uu____9258] in
  let mk_and_interp env conj uu____9274 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9291 =
      let uu____9292 =
        let uu____9296 =
          let uu____9297 =
            let uu____9303 =
              let uu____9304 =
                let uu____9307 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9307, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9304 in
            ([[l_and_a_b]], [aa; bb], uu____9303) in
          FStar_SMTEncoding_Util.mkForall uu____9297 in
        (uu____9296, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9292 in
    [uu____9291] in
  let mk_or_interp env disj uu____9331 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9348 =
      let uu____9349 =
        let uu____9353 =
          let uu____9354 =
            let uu____9360 =
              let uu____9361 =
                let uu____9364 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9364, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9361 in
            ([[l_or_a_b]], [aa; bb], uu____9360) in
          FStar_SMTEncoding_Util.mkForall uu____9354 in
        (uu____9353, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9349 in
    [uu____9348] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9405 =
      let uu____9406 =
        let uu____9410 =
          let uu____9411 =
            let uu____9417 =
              let uu____9418 =
                let uu____9421 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9421, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9418 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9417) in
          FStar_SMTEncoding_Util.mkForall uu____9411 in
        (uu____9410, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9406 in
    [uu____9405] in
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
    let uu____9468 =
      let uu____9469 =
        let uu____9473 =
          let uu____9474 =
            let uu____9480 =
              let uu____9481 =
                let uu____9484 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9484, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9481 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9480) in
          FStar_SMTEncoding_Util.mkForall uu____9474 in
        (uu____9473, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9469 in
    [uu____9468] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9529 =
      let uu____9530 =
        let uu____9534 =
          let uu____9535 =
            let uu____9541 =
              let uu____9542 =
                let uu____9545 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9545, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9542 in
            ([[l_imp_a_b]], [aa; bb], uu____9541) in
          FStar_SMTEncoding_Util.mkForall uu____9535 in
        (uu____9534, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9530 in
    [uu____9529] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9586 =
      let uu____9587 =
        let uu____9591 =
          let uu____9592 =
            let uu____9598 =
              let uu____9599 =
                let uu____9602 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9602, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9599 in
            ([[l_iff_a_b]], [aa; bb], uu____9598) in
          FStar_SMTEncoding_Util.mkForall uu____9592 in
        (uu____9591, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9587 in
    [uu____9586] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9636 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9636 in
    let uu____9638 =
      let uu____9639 =
        let uu____9643 =
          let uu____9644 =
            let uu____9650 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9650) in
          FStar_SMTEncoding_Util.mkForall uu____9644 in
        (uu____9643, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9639 in
    [uu____9638] in
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
      let uu____9690 =
        let uu____9694 =
          let uu____9696 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9696] in
        ("Valid", uu____9694) in
      FStar_SMTEncoding_Util.mkApp uu____9690 in
    let uu____9698 =
      let uu____9699 =
        let uu____9703 =
          let uu____9704 =
            let uu____9710 =
              let uu____9711 =
                let uu____9714 =
                  let uu____9715 =
                    let uu____9721 =
                      let uu____9724 =
                        let uu____9726 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9726] in
                      [uu____9724] in
                    let uu____9729 =
                      let uu____9730 =
                        let uu____9733 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9733, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9730 in
                    (uu____9721, [xx1], uu____9729) in
                  FStar_SMTEncoding_Util.mkForall uu____9715 in
                (uu____9714, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9711 in
            ([[l_forall_a_b]], [aa; bb], uu____9710) in
          FStar_SMTEncoding_Util.mkForall uu____9704 in
        (uu____9703, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9699 in
    [uu____9698] in
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
      let uu____9784 =
        let uu____9788 =
          let uu____9790 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9790] in
        ("Valid", uu____9788) in
      FStar_SMTEncoding_Util.mkApp uu____9784 in
    let uu____9792 =
      let uu____9793 =
        let uu____9797 =
          let uu____9798 =
            let uu____9804 =
              let uu____9805 =
                let uu____9808 =
                  let uu____9809 =
                    let uu____9815 =
                      let uu____9818 =
                        let uu____9820 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9820] in
                      [uu____9818] in
                    let uu____9823 =
                      let uu____9824 =
                        let uu____9827 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9827, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9824 in
                    (uu____9815, [xx1], uu____9823) in
                  FStar_SMTEncoding_Util.mkExists uu____9809 in
                (uu____9808, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9805 in
            ([[l_exists_a_b]], [aa; bb], uu____9804) in
          FStar_SMTEncoding_Util.mkForall uu____9798 in
        (uu____9797, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9793 in
    [uu____9792] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9863 =
      let uu____9864 =
        let uu____9868 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9869 = varops.mk_unique "typing_range_const" in
        (uu____9868, (Some "Range_const typing"), uu____9869) in
      FStar_SMTEncoding_Util.mkAssume uu____9864 in
    [uu____9863] in
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
          let uu____10131 =
            FStar_Util.find_opt
              (fun uu____10149  ->
                 match uu____10149 with
                 | (l,uu____10159) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____10131 with
          | None  -> []
          | Some (uu____10181,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10218 = encode_function_type_as_formula t env in
        match uu____10218 with
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
            let uu____10250 =
              (let uu____10251 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10251) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10250
            then
              let uu____10255 = new_term_constant_and_tok_from_lid env lid in
              match uu____10255 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10267 =
                      let uu____10268 = FStar_Syntax_Subst.compress t_norm in
                      uu____10268.FStar_Syntax_Syntax.n in
                    match uu____10267 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10273) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10290  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10293 -> [] in
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
              (let uu____10302 = prims.is lid in
               if uu____10302
               then
                 let vname = varops.new_fvar lid in
                 let uu____10307 = prims.mk lid vname in
                 match uu____10307 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10322 =
                    let uu____10328 = curried_arrow_formals_comp t_norm in
                    match uu____10328 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10339 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10339
                          then
                            let uu____10340 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___143_10341 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___143_10341.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___143_10341.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___143_10341.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___143_10341.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___143_10341.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___143_10341.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___143_10341.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___143_10341.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___143_10341.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___143_10341.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___143_10341.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___143_10341.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___143_10341.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___143_10341.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___143_10341.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___143_10341.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___143_10341.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___143_10341.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___143_10341.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___143_10341.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___143_10341.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___143_10341.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___143_10341.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___143_10341.FStar_TypeChecker_Env.proof_ns)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10340
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10348 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10348)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10322 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10375 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10375 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10388 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___114_10412  ->
                                     match uu___114_10412 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10415 =
                                           FStar_Util.prefix vars in
                                         (match uu____10415 with
                                          | (uu____10426,(xxsym,uu____10428))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10438 =
                                                let uu____10439 =
                                                  let uu____10443 =
                                                    let uu____10444 =
                                                      let uu____10450 =
                                                        let uu____10451 =
                                                          let uu____10454 =
                                                            let uu____10455 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10455 in
                                                          (vapp, uu____10454) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10451 in
                                                      ([[vapp]], vars,
                                                        uu____10450) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10444 in
                                                  (uu____10443,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10439 in
                                              [uu____10438])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10466 =
                                           FStar_Util.prefix vars in
                                         (match uu____10466 with
                                          | (uu____10477,(xxsym,uu____10479))
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
                                              let uu____10493 =
                                                let uu____10494 =
                                                  let uu____10498 =
                                                    let uu____10499 =
                                                      let uu____10505 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10505) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10499 in
                                                  (uu____10498,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10494 in
                                              [uu____10493])
                                     | uu____10514 -> [])) in
                           let uu____10515 = encode_binders None formals env1 in
                           (match uu____10515 with
                            | (vars,guards,env',decls1,uu____10531) ->
                                let uu____10538 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10543 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10543, decls1)
                                  | Some p ->
                                      let uu____10545 = encode_formula p env' in
                                      (match uu____10545 with
                                       | (g,ds) ->
                                           let uu____10552 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10552,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10538 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10561 =
                                         let uu____10565 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10565) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10561 in
                                     let uu____10570 =
                                       let vname_decl =
                                         let uu____10575 =
                                           let uu____10581 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10586  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10581,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10575 in
                                       let uu____10591 =
                                         let env2 =
                                           let uu___144_10595 = env1 in
                                           {
                                             bindings =
                                               (uu___144_10595.bindings);
                                             depth = (uu___144_10595.depth);
                                             tcenv = (uu___144_10595.tcenv);
                                             warn = (uu___144_10595.warn);
                                             cache = (uu___144_10595.cache);
                                             nolabels =
                                               (uu___144_10595.nolabels);
                                             use_zfuel_name =
                                               (uu___144_10595.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___144_10595.current_module_name)
                                           } in
                                         let uu____10596 =
                                           let uu____10597 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10597 in
                                         if uu____10596
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10591 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10607::uu____10608 ->
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
                                                   let uu____10631 =
                                                     let uu____10637 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10637) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10631 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10651 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10653 =
                                             match formals with
                                             | [] ->
                                                 let uu____10662 =
                                                   let uu____10663 =
                                                     let uu____10665 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_44  ->
                                                          Some _0_44)
                                                       uu____10665 in
                                                   push_free_var env1 lid
                                                     vname uu____10663 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10662)
                                             | uu____10668 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10673 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10673 in
                                                 let name_tok_corr =
                                                   let uu____10675 =
                                                     let uu____10679 =
                                                       let uu____10680 =
                                                         let uu____10686 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10686) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10680 in
                                                     (uu____10679,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10675 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10653 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10570 with
                                      | (decls2,env2) ->
                                          let uu____10710 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10715 =
                                              encode_term res_t1 env' in
                                            match uu____10715 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10723 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10723,
                                                  decls) in
                                          (match uu____10710 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10731 =
                                                   let uu____10735 =
                                                     let uu____10736 =
                                                       let uu____10742 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10742) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10736 in
                                                   (uu____10735,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10731 in
                                               let freshness =
                                                 let uu____10751 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10751
                                                 then
                                                   let uu____10754 =
                                                     let uu____10755 =
                                                       let uu____10761 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
                                                       let uu____10767 =
                                                         varops.next_id () in
                                                       (vname, uu____10761,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10767) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10755 in
                                                   let uu____10769 =
                                                     let uu____10771 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10771] in
                                                   uu____10754 :: uu____10769
                                                 else [] in
                                               let g =
                                                 let uu____10775 =
                                                   let uu____10777 =
                                                     let uu____10779 =
                                                       let uu____10781 =
                                                         let uu____10783 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10783 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10781 in
                                                     FStar_List.append decls3
                                                       uu____10779 in
                                                   FStar_List.append decls2
                                                     uu____10777 in
                                                 FStar_List.append decls11
                                                   uu____10775 in
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
          let uu____10805 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10805 with
          | None  ->
              let uu____10828 = encode_free_var env x t t_norm [] in
              (match uu____10828 with
               | (decls,env1) ->
                   let uu____10843 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10843 with
                    | (n1,x',uu____10862) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10874) -> ((n1, x1), [], env)
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
          let uu____10907 = encode_free_var env lid t tt quals in
          match uu____10907 with
          | (decls,env1) ->
              let uu____10918 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10918
              then
                let uu____10922 =
                  let uu____10924 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10924 in
                (uu____10922, env1)
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
             (fun uu____10952  ->
                fun lb  ->
                  match uu____10952 with
                  | (decls,env1) ->
                      let uu____10964 =
                        let uu____10968 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10968
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10964 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10982 = FStar_Syntax_Util.head_and_args t in
    match uu____10982 with
    | (hd1,args) ->
        let uu____11008 =
          let uu____11009 = FStar_Syntax_Util.un_uinst hd1 in
          uu____11009.FStar_Syntax_Syntax.n in
        (match uu____11008 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____11013,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____11026 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____11041  ->
      fun quals  ->
        match uu____11041 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____11090 = FStar_Util.first_N nbinders formals in
              match uu____11090 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11130  ->
                         fun uu____11131  ->
                           match (uu____11130, uu____11131) with
                           | ((formal,uu____11141),(binder,uu____11143)) ->
                               let uu____11148 =
                                 let uu____11153 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11153) in
                               FStar_Syntax_Syntax.NT uu____11148) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11158 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11172  ->
                              match uu____11172 with
                              | (x,i) ->
                                  let uu____11179 =
                                    let uu___145_11180 = x in
                                    let uu____11181 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___145_11180.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___145_11180.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11181
                                    } in
                                  (uu____11179, i))) in
                    FStar_All.pipe_right uu____11158
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11193 =
                      let uu____11195 =
                        let uu____11196 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11196.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_45  -> Some _0_45)
                        uu____11195 in
                    let uu____11200 =
                      let uu____11201 = FStar_Syntax_Subst.compress body in
                      let uu____11202 =
                        let uu____11203 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11203 in
                      FStar_Syntax_Syntax.extend_app_n uu____11201
                        uu____11202 in
                    uu____11200 uu____11193 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11245 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11245
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___146_11246 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___146_11246.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___146_11246.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___146_11246.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___146_11246.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___146_11246.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___146_11246.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___146_11246.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___146_11246.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___146_11246.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___146_11246.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___146_11246.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___146_11246.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___146_11246.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___146_11246.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___146_11246.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___146_11246.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___146_11246.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___146_11246.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___146_11246.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___146_11246.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___146_11246.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___146_11246.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___146_11246.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___146_11246.FStar_TypeChecker_Env.proof_ns)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11267 = FStar_Syntax_Util.abs_formals e in
                match uu____11267 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11316::uu____11317 ->
                         let uu____11325 =
                           let uu____11326 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11326.FStar_Syntax_Syntax.n in
                         (match uu____11325 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11353 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11353 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11379 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11379
                                   then
                                     let uu____11397 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11397 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11443  ->
                                                   fun uu____11444  ->
                                                     match (uu____11443,
                                                             uu____11444)
                                                     with
                                                     | ((x,uu____11454),
                                                        (b,uu____11456)) ->
                                                         let uu____11461 =
                                                           let uu____11466 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11466) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11461)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11468 =
                                            let uu____11479 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11479) in
                                          (uu____11468, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11514 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11514 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11566) ->
                              let uu____11571 =
                                let uu____11582 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____11582 in
                              (uu____11571, true)
                          | uu____11615 when Prims.op_Negation norm1 ->
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
                          | uu____11617 ->
                              let uu____11618 =
                                let uu____11619 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11620 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11619
                                  uu____11620 in
                              failwith uu____11618)
                     | uu____11633 ->
                         let uu____11634 =
                           let uu____11635 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11635.FStar_Syntax_Syntax.n in
                         (match uu____11634 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11662 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11662 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11680 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11680 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11728 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11756 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11756
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11763 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11804  ->
                            fun lb  ->
                              match uu____11804 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11855 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11855
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11858 =
                                      let uu____11866 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11866
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11858 with
                                    | (tok,decl,env2) ->
                                        let uu____11891 =
                                          let uu____11898 =
                                            let uu____11904 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11904, tok) in
                                          uu____11898 :: toks in
                                        (uu____11891, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11763 with
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
                        | uu____12006 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____12011 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____12011 vars)
                            else
                              (let uu____12013 =
                                 let uu____12017 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____12017) in
                               FStar_SMTEncoding_Util.mkApp uu____12013) in
                      let uu____12022 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___115_12024  ->
                                 match uu___115_12024 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____12025 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____12028 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____12028))) in
                      if uu____12022
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____12048;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____12050;
                                FStar_Syntax_Syntax.lbeff = uu____12051;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____12092 =
                                 let uu____12096 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____12096 with
                                 | (tcenv',uu____12107,e_t) ->
                                     let uu____12111 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12118 -> failwith "Impossible" in
                                     (match uu____12111 with
                                      | (e1,t_norm1) ->
                                          ((let uu___149_12127 = env1 in
                                            {
                                              bindings =
                                                (uu___149_12127.bindings);
                                              depth = (uu___149_12127.depth);
                                              tcenv = tcenv';
                                              warn = (uu___149_12127.warn);
                                              cache = (uu___149_12127.cache);
                                              nolabels =
                                                (uu___149_12127.nolabels);
                                              use_zfuel_name =
                                                (uu___149_12127.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___149_12127.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___149_12127.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____12092 with
                                | (env',e1,t_norm1) ->
                                    let uu____12134 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____12134 with
                                     | ((binders,body,uu____12146,uu____12147),curry)
                                         ->
                                         ((let uu____12154 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____12154
                                           then
                                             let uu____12155 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12156 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12155 uu____12156
                                           else ());
                                          (let uu____12158 =
                                             encode_binders None binders env' in
                                           match uu____12158 with
                                           | (vars,guards,env'1,binder_decls,uu____12174)
                                               ->
                                               let body1 =
                                                 let uu____12182 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12182
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12185 =
                                                 let uu____12190 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12190
                                                 then
                                                   let uu____12196 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12197 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12196, uu____12197)
                                                 else
                                                   (let uu____12203 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12203)) in
                                               (match uu____12185 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12217 =
                                                        let uu____12221 =
                                                          let uu____12222 =
                                                            let uu____12228 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12228) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12222 in
                                                        let uu____12234 =
                                                          let uu____12236 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12236 in
                                                        (uu____12221,
                                                          uu____12234,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12217 in
                                                    let uu____12238 =
                                                      let uu____12240 =
                                                        let uu____12242 =
                                                          let uu____12244 =
                                                            let uu____12246 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12246 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12244 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12242 in
                                                      FStar_List.append
                                                        decls1 uu____12240 in
                                                    (uu____12238, env1))))))
                           | uu____12249 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12268 = varops.fresh "fuel" in
                             (uu____12268, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12271 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12310  ->
                                     fun uu____12311  ->
                                       match (uu____12310, uu____12311) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12393 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12393 in
                                           let gtok =
                                             let uu____12395 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12395 in
                                           let env3 =
                                             let uu____12397 =
                                               let uu____12399 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_46  -> Some _0_46)
                                                 uu____12399 in
                                             push_free_var env2 flid gtok
                                               uu____12397 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12271 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12485
                                 t_norm uu____12487 =
                                 match (uu____12485, uu____12487) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12514;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12515;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12532 =
                                       let uu____12536 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12536 with
                                       | (tcenv',uu____12551,e_t) ->
                                           let uu____12555 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12562 ->
                                                 failwith "Impossible" in
                                           (match uu____12555 with
                                            | (e1,t_norm1) ->
                                                ((let uu___150_12571 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___150_12571.bindings);
                                                    depth =
                                                      (uu___150_12571.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___150_12571.warn);
                                                    cache =
                                                      (uu___150_12571.cache);
                                                    nolabels =
                                                      (uu___150_12571.nolabels);
                                                    use_zfuel_name =
                                                      (uu___150_12571.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___150_12571.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___150_12571.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12532 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12581 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12581
                                            then
                                              let uu____12582 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12583 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12584 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12582 uu____12583
                                                uu____12584
                                            else ());
                                           (let uu____12586 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12586 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12608 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12608
                                                  then
                                                    let uu____12609 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12610 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12611 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12612 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12609 uu____12610
                                                      uu____12611 uu____12612
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12616 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12616 with
                                                  | (vars,guards,env'1,binder_decls,uu____12634)
                                                      ->
                                                      let decl_g =
                                                        let uu____12642 =
                                                          let uu____12648 =
                                                            let uu____12650 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12650 in
                                                          (g, uu____12648,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12642 in
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
                                                        let uu____12665 =
                                                          let uu____12669 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12669) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12665 in
                                                      let gsapp =
                                                        let uu____12675 =
                                                          let uu____12679 =
                                                            let uu____12681 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12681 ::
                                                              vars_tm in
                                                          (g, uu____12679) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12675 in
                                                      let gmax =
                                                        let uu____12685 =
                                                          let uu____12689 =
                                                            let uu____12691 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12691 ::
                                                              vars_tm in
                                                          (g, uu____12689) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12685 in
                                                      let body1 =
                                                        let uu____12695 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12695
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12697 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12697 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12708
                                                               =
                                                               let uu____12712
                                                                 =
                                                                 let uu____12713
                                                                   =
                                                                   let uu____12721
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
                                                                    uu____12721) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12713 in
                                                               let uu____12732
                                                                 =
                                                                 let uu____12734
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12734 in
                                                               (uu____12712,
                                                                 uu____12732,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12708 in
                                                           let eqn_f =
                                                             let uu____12737
                                                               =
                                                               let uu____12741
                                                                 =
                                                                 let uu____12742
                                                                   =
                                                                   let uu____12748
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12748) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12742 in
                                                               (uu____12741,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12737 in
                                                           let eqn_g' =
                                                             let uu____12756
                                                               =
                                                               let uu____12760
                                                                 =
                                                                 let uu____12761
                                                                   =
                                                                   let uu____12767
                                                                    =
                                                                    let uu____12768
                                                                    =
                                                                    let uu____12771
                                                                    =
                                                                    let uu____12772
                                                                    =
                                                                    let uu____12776
                                                                    =
                                                                    let uu____12778
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12778
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12776) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12772 in
                                                                    (gsapp,
                                                                    uu____12771) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12768 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12767) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12761 in
                                                               (uu____12760,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12756 in
                                                           let uu____12790 =
                                                             let uu____12795
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12795
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12812)
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
                                                                    let uu____12827
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12827
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12830
                                                                    =
                                                                    let uu____12834
                                                                    =
                                                                    let uu____12835
                                                                    =
                                                                    let uu____12841
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12841) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12835 in
                                                                    (uu____12834,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12830 in
                                                                 let uu____12852
                                                                   =
                                                                   let uu____12856
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12856
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12864
                                                                    =
                                                                    let uu____12866
                                                                    =
                                                                    let uu____12867
                                                                    =
                                                                    let uu____12871
                                                                    =
                                                                    let uu____12872
                                                                    =
                                                                    let uu____12878
                                                                    =
                                                                    let uu____12879
                                                                    =
                                                                    let uu____12882
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12882,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12879 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12878) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12872 in
                                                                    (uu____12871,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12867 in
                                                                    [uu____12866] in
                                                                    (d3,
                                                                    uu____12864) in
                                                                 (match uu____12852
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12790
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
                               let uu____12917 =
                                 let uu____12924 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12960  ->
                                      fun uu____12961  ->
                                        match (uu____12960, uu____12961) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____13047 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____13047 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12924 in
                               (match uu____12917 with
                                | (decls2,eqns,env01) ->
                                    let uu____13087 =
                                      let isDeclFun uu___116_13095 =
                                        match uu___116_13095 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____13096 -> true
                                        | uu____13102 -> false in
                                      let uu____13103 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____13103
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____13087 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____13130 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____13130
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
        let uu____13163 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13163 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____13166 = encode_sigelt' env se in
      match uu____13166 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13176 =
                  let uu____13177 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13177 in
                [uu____13176]
            | uu____13178 ->
                let uu____13179 =
                  let uu____13181 =
                    let uu____13182 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13182 in
                  uu____13181 :: g in
                let uu____13183 =
                  let uu____13185 =
                    let uu____13186 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13186 in
                  [uu____13185] in
                FStar_List.append uu____13179 uu____13183 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13194 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13197 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13199 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13201 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13209 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13212 =
            let uu____13213 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13213 Prims.op_Negation in
          if uu____13212
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13233 ->
                   let uu____13234 =
                     let uu____13237 =
                       let uu____13238 =
                         let uu____13253 =
                           FStar_All.pipe_left (fun _0_47  -> Some _0_47)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13253) in
                       FStar_Syntax_Syntax.Tm_abs uu____13238 in
                     FStar_Syntax_Syntax.mk uu____13237 in
                   uu____13234 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13306 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13306 with
               | (aname,atok,env2) ->
                   let uu____13316 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13316 with
                    | (formals,uu____13326) ->
                        let uu____13333 =
                          let uu____13336 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13336 env2 in
                        (match uu____13333 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13344 =
                                 let uu____13345 =
                                   let uu____13351 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13359  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13351,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13345 in
                               [uu____13344;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13366 =
                               let aux uu____13395 uu____13396 =
                                 match (uu____13395, uu____13396) with
                                 | ((bv,uu____13423),(env3,acc_sorts,acc)) ->
                                     let uu____13444 = gen_term_var env3 bv in
                                     (match uu____13444 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13366 with
                              | (uu____13482,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13496 =
                                      let uu____13500 =
                                        let uu____13501 =
                                          let uu____13507 =
                                            let uu____13508 =
                                              let uu____13511 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13511) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13508 in
                                          ([[app]], xs_sorts, uu____13507) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13501 in
                                      (uu____13500, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13496 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13523 =
                                      let uu____13527 =
                                        let uu____13528 =
                                          let uu____13534 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13534) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13528 in
                                      (uu____13527,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13523 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13544 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13544 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13560,uu____13561)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13562 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13562 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13573,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13578 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___117_13580  ->
                      match uu___117_13580 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13581 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13584 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13585 -> false)) in
            Prims.op_Negation uu____13578 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13591 = encode_top_level_val env fv t quals in
             match uu____13591 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13603 =
                   let uu____13605 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13605 in
                 (uu____13603, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13610 = encode_formula f env in
          (match uu____13610 with
           | (f1,decls) ->
               let g =
                 let uu____13619 =
                   let uu____13620 =
                     let uu____13624 =
                       let uu____13626 =
                         let uu____13627 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13627 in
                       Some uu____13626 in
                     let uu____13628 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13624, uu____13628) in
                   FStar_SMTEncoding_Util.mkAssume uu____13620 in
                 [uu____13619] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13632,uu____13633) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13639 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13646 =
                       let uu____13651 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13651.FStar_Syntax_Syntax.fv_name in
                     uu____13646.FStar_Syntax_Syntax.v in
                   let uu____13655 =
                     let uu____13656 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13656 in
                   if uu____13655
                   then
                     let val_decl =
                       let uu___151_13671 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___151_13671.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___151_13671.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___151_13671.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13675 = encode_sigelt' env1 val_decl in
                     match uu____13675 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____13639 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13692,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13694;
                          FStar_Syntax_Syntax.lbtyp = uu____13695;
                          FStar_Syntax_Syntax.lbeff = uu____13696;
                          FStar_Syntax_Syntax.lbdef = uu____13697;_}::[]),uu____13698,uu____13699)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13713 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13713 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13736 =
                   let uu____13738 =
                     let uu____13739 =
                       let uu____13743 =
                         let uu____13744 =
                           let uu____13750 =
                             let uu____13751 =
                               let uu____13754 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13754) in
                             FStar_SMTEncoding_Util.mkEq uu____13751 in
                           ([[b2t_x]], [xx], uu____13750) in
                         FStar_SMTEncoding_Util.mkForall uu____13744 in
                       (uu____13743, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13739 in
                   [uu____13738] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13736 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13771,uu____13772,uu____13773)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___118_13779  ->
                  match uu___118_13779 with
                  | FStar_Syntax_Syntax.Discriminator uu____13780 -> true
                  | uu____13781 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13783,lids,uu____13785) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13792 =
                     let uu____13793 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13793.FStar_Ident.idText in
                   uu____13792 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___119_13795  ->
                     match uu___119_13795 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13796 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13799,uu____13800)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___120_13810  ->
                  match uu___120_13810 with
                  | FStar_Syntax_Syntax.Projector uu____13811 -> true
                  | uu____13814 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13821 = try_lookup_free_var env l in
          (match uu____13821 with
           | Some uu____13825 -> ([], env)
           | None  ->
               let se1 =
                 let uu___152_13828 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___152_13828.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___152_13828.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13834,uu____13835) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13847) ->
          let uu____13852 = encode_sigelts env ses in
          (match uu____13852 with
           | (g,env1) ->
               let uu____13862 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___121_13872  ->
                         match uu___121_13872 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13873;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13874;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13875;_}
                             -> false
                         | uu____13877 -> true)) in
               (match uu____13862 with
                | (g',inversions) ->
                    let uu____13886 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___122_13896  ->
                              match uu___122_13896 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13897 ->
                                  true
                              | uu____13903 -> false)) in
                    (match uu____13886 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13914,tps,k,uu____13917,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___123_13927  ->
                    match uu___123_13927 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13928 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13935 = c in
              match uu____13935 with
              | (name,args,uu____13939,uu____13940,uu____13941) ->
                  let uu____13944 =
                    let uu____13945 =
                      let uu____13951 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13958  ->
                                match uu____13958 with
                                | (uu____13962,sort,uu____13964) -> sort)) in
                      (name, uu____13951, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13945 in
                  [uu____13944]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13982 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13985 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13985 FStar_Option.isNone)) in
            if uu____13982
            then []
            else
              (let uu____14002 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____14002 with
               | (xxsym,xx) ->
                   let uu____14008 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____14019  ->
                             fun l  ->
                               match uu____14019 with
                               | (out,decls) ->
                                   let uu____14031 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____14031 with
                                    | (uu____14037,data_t) ->
                                        let uu____14039 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____14039 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____14068 =
                                                 let uu____14069 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____14069.FStar_Syntax_Syntax.n in
                                               match uu____14068 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____14077,indices) ->
                                                   indices
                                               | uu____14093 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____14105  ->
                                                         match uu____14105
                                                         with
                                                         | (x,uu____14109) ->
                                                             let uu____14110
                                                               =
                                                               let uu____14111
                                                                 =
                                                                 let uu____14115
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____14115,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14111 in
                                                             push_term_var
                                                               env1 x
                                                               uu____14110)
                                                    env) in
                                             let uu____14117 =
                                               encode_args indices env1 in
                                             (match uu____14117 with
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
                                                      let uu____14137 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14145
                                                                 =
                                                                 let uu____14148
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____14148,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14145)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____14137
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____14150 =
                                                      let uu____14151 =
                                                        let uu____14154 =
                                                          let uu____14155 =
                                                            let uu____14158 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____14158,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14155 in
                                                        (out, uu____14154) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14151 in
                                                    (uu____14150,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____14008 with
                    | (data_ax,decls) ->
                        let uu____14166 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14166 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14177 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14177 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14180 =
                                 let uu____14184 =
                                   let uu____14185 =
                                     let uu____14191 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14199 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14191,
                                       uu____14199) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14185 in
                                 let uu____14207 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14184, (Some "inversion axiom"),
                                   uu____14207) in
                               FStar_SMTEncoding_Util.mkAssume uu____14180 in
                             let pattern_guarded_inversion =
                               let uu____14211 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14211
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14219 =
                                   let uu____14220 =
                                     let uu____14224 =
                                       let uu____14225 =
                                         let uu____14231 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14239 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14231, uu____14239) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14225 in
                                     let uu____14247 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14224, (Some "inversion axiom"),
                                       uu____14247) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14220 in
                                 [uu____14219]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14250 =
            let uu____14258 =
              let uu____14259 = FStar_Syntax_Subst.compress k in
              uu____14259.FStar_Syntax_Syntax.n in
            match uu____14258 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14288 -> (tps, k) in
          (match uu____14250 with
           | (formals,res) ->
               let uu____14303 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14303 with
                | (formals1,res1) ->
                    let uu____14310 = encode_binders None formals1 env in
                    (match uu____14310 with
                     | (vars,guards,env',binder_decls,uu____14325) ->
                         let uu____14332 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14332 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14345 =
                                  let uu____14349 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14349) in
                                FStar_SMTEncoding_Util.mkApp uu____14345 in
                              let uu____14354 =
                                let tname_decl =
                                  let uu____14360 =
                                    let uu____14361 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14376  ->
                                              match uu____14376 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14384 = varops.next_id () in
                                    (tname, uu____14361,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14384, false) in
                                  constructor_or_logic_type_decl uu____14360 in
                                let uu____14389 =
                                  match vars with
                                  | [] ->
                                      let uu____14396 =
                                        let uu____14397 =
                                          let uu____14399 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_48  -> Some _0_48)
                                            uu____14399 in
                                        push_free_var env1 t tname
                                          uu____14397 in
                                      ([], uu____14396)
                                  | uu____14403 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14409 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14409 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14418 =
                                          let uu____14422 =
                                            let uu____14423 =
                                              let uu____14431 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14431) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14423 in
                                          (uu____14422,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14418 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14389 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14354 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14454 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14454 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14468 =
                                               let uu____14469 =
                                                 let uu____14473 =
                                                   let uu____14474 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14474 in
                                                 (uu____14473,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14469 in
                                             [uu____14468]
                                           else [] in
                                         let uu____14477 =
                                           let uu____14479 =
                                             let uu____14481 =
                                               let uu____14482 =
                                                 let uu____14486 =
                                                   let uu____14487 =
                                                     let uu____14493 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14493) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14487 in
                                                 (uu____14486, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14482 in
                                             [uu____14481] in
                                           FStar_List.append karr uu____14479 in
                                         FStar_List.append decls1 uu____14477 in
                                   let aux =
                                     let uu____14502 =
                                       let uu____14504 =
                                         inversion_axioms tapp vars in
                                       let uu____14506 =
                                         let uu____14508 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14508] in
                                       FStar_List.append uu____14504
                                         uu____14506 in
                                     FStar_List.append kindingAx uu____14502 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14513,uu____14514,uu____14515,uu____14516,uu____14517)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14522,t,uu____14524,n_tps,uu____14526) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14531 = new_term_constant_and_tok_from_lid env d in
          (match uu____14531 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14542 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14542 with
                | (formals,t_res) ->
                    let uu____14564 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14564 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14573 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14573 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14611 =
                                            mk_term_projector_name d x in
                                          (uu____14611,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14613 =
                                  let uu____14623 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14623, true) in
                                FStar_All.pipe_right uu____14613
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
                              let uu____14645 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14645 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14653::uu____14654 ->
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
                                         let uu____14679 =
                                           let uu____14685 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14685) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14679
                                     | uu____14698 -> tok_typing in
                                   let uu____14703 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14703 with
                                    | (vars',guards',env'',decls_formals,uu____14718)
                                        ->
                                        let uu____14725 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14725 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14744 ->
                                                   let uu____14748 =
                                                     let uu____14749 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14749 in
                                                   [uu____14748] in
                                             let encode_elim uu____14756 =
                                               let uu____14757 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14757 with
                                               | (head1,args) ->
                                                   let uu____14786 =
                                                     let uu____14787 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14787.FStar_Syntax_Syntax.n in
                                                   (match uu____14786 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____14794;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14795;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14796;_},uu____14797)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14807 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14807
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
                                                                 | uu____14833
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14841
                                                                    =
                                                                    let uu____14842
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14842 in
                                                                    if
                                                                    uu____14841
                                                                    then
                                                                    let uu____14849
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14849]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14851
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14864
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14864
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14886
                                                                    =
                                                                    let uu____14890
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14890 in
                                                                    (match uu____14886
                                                                    with
                                                                    | 
                                                                    (uu____14897,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14903
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14903
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14905
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14905
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
                                                             (match uu____14851
                                                              with
                                                              | (uu____14913,arg_vars,elim_eqns_or_guards,uu____14916)
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
                                                                    let uu____14935
                                                                    =
                                                                    let uu____14939
                                                                    =
                                                                    let uu____14940
                                                                    =
                                                                    let uu____14946
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14952
                                                                    =
                                                                    let uu____14953
                                                                    =
                                                                    let uu____14956
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14956) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14953 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14946,
                                                                    uu____14952) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14940 in
                                                                    (uu____14939,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14935 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14969
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14969,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14971
                                                                    =
                                                                    let uu____14975
                                                                    =
                                                                    let uu____14976
                                                                    =
                                                                    let uu____14982
                                                                    =
                                                                    let uu____14985
                                                                    =
                                                                    let uu____14987
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14987] in
                                                                    [uu____14985] in
                                                                    let uu____14990
                                                                    =
                                                                    let uu____14991
                                                                    =
                                                                    let uu____14994
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14995
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14994,
                                                                    uu____14995) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14991 in
                                                                    (uu____14982,
                                                                    [x],
                                                                    uu____14990) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14976 in
                                                                    let uu____15005
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14975,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15005) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14971
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15010
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
                                                                    (let uu____15025
                                                                    =
                                                                    let uu____15026
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15026
                                                                    dapp1 in
                                                                    [uu____15025]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15010
                                                                    FStar_List.flatten in
                                                                    let uu____15030
                                                                    =
                                                                    let uu____15034
                                                                    =
                                                                    let uu____15035
                                                                    =
                                                                    let uu____15041
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15047
                                                                    =
                                                                    let uu____15048
                                                                    =
                                                                    let uu____15051
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15051) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15048 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15041,
                                                                    uu____15047) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15035 in
                                                                    (uu____15034,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15030) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____15067 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15067
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
                                                                 | uu____15093
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15101
                                                                    =
                                                                    let uu____15102
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15102 in
                                                                    if
                                                                    uu____15101
                                                                    then
                                                                    let uu____15109
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15109]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15111
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15124
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15124
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15146
                                                                    =
                                                                    let uu____15150
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15150 in
                                                                    (match uu____15146
                                                                    with
                                                                    | 
                                                                    (uu____15157,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15163
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15163
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15165
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15165
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
                                                             (match uu____15111
                                                              with
                                                              | (uu____15173,arg_vars,elim_eqns_or_guards,uu____15176)
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
                                                                    let uu____15195
                                                                    =
                                                                    let uu____15199
                                                                    =
                                                                    let uu____15200
                                                                    =
                                                                    let uu____15206
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15212
                                                                    =
                                                                    let uu____15213
                                                                    =
                                                                    let uu____15216
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15216) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15213 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15206,
                                                                    uu____15212) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15200 in
                                                                    (uu____15199,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15195 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15229
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15229,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15231
                                                                    =
                                                                    let uu____15235
                                                                    =
                                                                    let uu____15236
                                                                    =
                                                                    let uu____15242
                                                                    =
                                                                    let uu____15245
                                                                    =
                                                                    let uu____15247
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15247] in
                                                                    [uu____15245] in
                                                                    let uu____15250
                                                                    =
                                                                    let uu____15251
                                                                    =
                                                                    let uu____15254
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15255
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15254,
                                                                    uu____15255) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15251 in
                                                                    (uu____15242,
                                                                    [x],
                                                                    uu____15250) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15236 in
                                                                    let uu____15265
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15235,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15265) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15231
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15270
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
                                                                    (let uu____15285
                                                                    =
                                                                    let uu____15286
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15286
                                                                    dapp1 in
                                                                    [uu____15285]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15270
                                                                    FStar_List.flatten in
                                                                    let uu____15290
                                                                    =
                                                                    let uu____15294
                                                                    =
                                                                    let uu____15295
                                                                    =
                                                                    let uu____15301
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15307
                                                                    =
                                                                    let uu____15308
                                                                    =
                                                                    let uu____15311
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15311) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15308 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15301,
                                                                    uu____15307) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15295 in
                                                                    (uu____15294,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15290) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15321 ->
                                                        ((let uu____15323 =
                                                            let uu____15324 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15325 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15324
                                                              uu____15325 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15323);
                                                         ([], []))) in
                                             let uu____15328 = encode_elim () in
                                             (match uu____15328 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15340 =
                                                      let uu____15342 =
                                                        let uu____15344 =
                                                          let uu____15346 =
                                                            let uu____15348 =
                                                              let uu____15349
                                                                =
                                                                let uu____15355
                                                                  =
                                                                  let uu____15357
                                                                    =
                                                                    let uu____15358
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15358 in
                                                                  Some
                                                                    uu____15357 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15355) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15349 in
                                                            [uu____15348] in
                                                          let uu____15361 =
                                                            let uu____15363 =
                                                              let uu____15365
                                                                =
                                                                let uu____15367
                                                                  =
                                                                  let uu____15369
                                                                    =
                                                                    let uu____15371
                                                                    =
                                                                    let uu____15373
                                                                    =
                                                                    let uu____15374
                                                                    =
                                                                    let uu____15378
                                                                    =
                                                                    let uu____15379
                                                                    =
                                                                    let uu____15385
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15385) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15379 in
                                                                    (uu____15378,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15374 in
                                                                    let uu____15392
                                                                    =
                                                                    let uu____15394
                                                                    =
                                                                    let uu____15395
                                                                    =
                                                                    let uu____15399
                                                                    =
                                                                    let uu____15400
                                                                    =
                                                                    let uu____15406
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____15412
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15406,
                                                                    uu____15412) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15400 in
                                                                    (uu____15399,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15395 in
                                                                    [uu____15394] in
                                                                    uu____15373
                                                                    ::
                                                                    uu____15392 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15371 in
                                                                  FStar_List.append
                                                                    uu____15369
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15367 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15365 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15363 in
                                                          FStar_List.append
                                                            uu____15346
                                                            uu____15361 in
                                                        FStar_List.append
                                                          decls3 uu____15344 in
                                                      FStar_List.append
                                                        decls2 uu____15342 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15340 in
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
           (fun uu____15433  ->
              fun se  ->
                match uu____15433 with
                | (g,env1) ->
                    let uu____15445 = encode_sigelt env1 se in
                    (match uu____15445 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15481 =
        match uu____15481 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15499 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____15504 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15504
                   then
                     let uu____15505 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15506 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15507 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15505 uu____15506 uu____15507
                   else ());
                  (let uu____15509 = encode_term t1 env1 in
                   match uu____15509 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15519 =
                         let uu____15523 =
                           let uu____15524 =
                             let uu____15525 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15525
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15524 in
                         new_term_constant_from_string env1 x uu____15523 in
                       (match uu____15519 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15536 = FStar_Options.log_queries () in
                              if uu____15536
                              then
                                let uu____15538 =
                                  let uu____15539 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15540 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15541 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15539 uu____15540 uu____15541 in
                                Some uu____15538
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15552,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15561 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15561 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15574,se,uu____15576) ->
                 let uu____15579 = encode_sigelt env1 se in
                 (match uu____15579 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15589,se) ->
                 let uu____15593 = encode_sigelt env1 se in
                 (match uu____15593 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15603 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15603 with | (uu____15615,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15660  ->
            match uu____15660 with
            | (l,uu____15667,uu____15668) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15689  ->
            match uu____15689 with
            | (l,uu____15697,uu____15698) ->
                let uu____15703 =
                  FStar_All.pipe_left
                    (fun _0_49  -> FStar_SMTEncoding_Term.Echo _0_49) (
                    fst l) in
                let uu____15704 =
                  let uu____15706 =
                    let uu____15707 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15707 in
                  [uu____15706] in
                uu____15703 :: uu____15704)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15718 =
      let uu____15720 =
        let uu____15721 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15723 =
          let uu____15724 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15724 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15721;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15723
        } in
      [uu____15720] in
    FStar_ST.write last_env uu____15718
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15734 = FStar_ST.read last_env in
      match uu____15734 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15740 ->
          let uu___153_15742 = e in
          let uu____15743 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___153_15742.bindings);
            depth = (uu___153_15742.depth);
            tcenv;
            warn = (uu___153_15742.warn);
            cache = (uu___153_15742.cache);
            nolabels = (uu___153_15742.nolabels);
            use_zfuel_name = (uu___153_15742.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___153_15742.encode_non_total_function_typ);
            current_module_name = uu____15743
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15747 = FStar_ST.read last_env in
    match uu____15747 with
    | [] -> failwith "Empty env stack"
    | uu____15752::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15760  ->
    let uu____15761 = FStar_ST.read last_env in
    match uu____15761 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___154_15772 = hd1 in
          {
            bindings = (uu___154_15772.bindings);
            depth = (uu___154_15772.depth);
            tcenv = (uu___154_15772.tcenv);
            warn = (uu___154_15772.warn);
            cache = refs;
            nolabels = (uu___154_15772.nolabels);
            use_zfuel_name = (uu___154_15772.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15772.encode_non_total_function_typ);
            current_module_name = (uu___154_15772.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15778  ->
    let uu____15779 = FStar_ST.read last_env in
    match uu____15779 with
    | [] -> failwith "Popping an empty stack"
    | uu____15784::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15792  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15795  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15798  ->
    let uu____15799 = FStar_ST.read last_env in
    match uu____15799 with
    | hd1::uu____15805::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15811 -> failwith "Impossible"
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
        | (uu____15860::uu____15861,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___155_15865 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___155_15865.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___155_15865.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___155_15865.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15866 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15877 =
        let uu____15879 =
          let uu____15880 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15880 in
        let uu____15881 = open_fact_db_tags env in uu____15879 :: uu____15881 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15877
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
      let uu____15896 = encode_sigelt env se in
      match uu____15896 with
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
        let uu____15921 = FStar_Options.log_queries () in
        if uu____15921
        then
          let uu____15923 =
            let uu____15924 =
              let uu____15925 =
                let uu____15926 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15926 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15925 in
            FStar_SMTEncoding_Term.Caption uu____15924 in
          uu____15923 :: decls
        else decls in
      let env =
        let uu____15933 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15933 tcenv in
      let uu____15934 = encode_top_level_facts env se in
      match uu____15934 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15943 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15943))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15954 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15954
       then
         let uu____15955 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15955
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15976  ->
                 fun se  ->
                   match uu____15976 with
                   | (g,env2) ->
                       let uu____15988 = encode_top_level_facts env2 se in
                       (match uu____15988 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____16001 =
         encode_signature
           (let uu___156_16005 = env in
            {
              bindings = (uu___156_16005.bindings);
              depth = (uu___156_16005.depth);
              tcenv = (uu___156_16005.tcenv);
              warn = false;
              cache = (uu___156_16005.cache);
              nolabels = (uu___156_16005.nolabels);
              use_zfuel_name = (uu___156_16005.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_16005.encode_non_total_function_typ);
              current_module_name = (uu___156_16005.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____16001 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____16017 = FStar_Options.log_queries () in
             if uu____16017
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___157_16022 = env1 in
               {
                 bindings = (uu___157_16022.bindings);
                 depth = (uu___157_16022.depth);
                 tcenv = (uu___157_16022.tcenv);
                 warn = true;
                 cache = (uu___157_16022.cache);
                 nolabels = (uu___157_16022.nolabels);
                 use_zfuel_name = (uu___157_16022.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___157_16022.encode_non_total_function_typ);
                 current_module_name = (uu___157_16022.current_module_name)
               });
            (let uu____16024 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____16024
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
        (let uu____16059 =
           let uu____16060 = FStar_TypeChecker_Env.current_module tcenv in
           uu____16060.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16059);
        (let env =
           let uu____16062 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____16062 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____16069 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16090 = aux rest in
                 (match uu____16090 with
                  | (out,rest1) ->
                      let t =
                        let uu____16108 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____16108 with
                        | Some uu____16112 ->
                            let uu____16113 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16113
                              x.FStar_Syntax_Syntax.sort
                        | uu____16114 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____16117 =
                        let uu____16119 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___158_16120 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_16120.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_16120.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16119 :: out in
                      (uu____16117, rest1))
             | uu____16123 -> ([], bindings1) in
           let uu____16127 = aux bindings in
           match uu____16127 with
           | (closing,bindings1) ->
               let uu____16141 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16141, bindings1) in
         match uu____16069 with
         | (q1,bindings1) ->
             let uu____16154 =
               let uu____16157 =
                 FStar_List.filter
                   (fun uu___124_16159  ->
                      match uu___124_16159 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16160 ->
                          false
                      | uu____16164 -> true) bindings1 in
               encode_env_bindings env uu____16157 in
             (match uu____16154 with
              | (env_decls,env1) ->
                  ((let uu____16175 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16175
                    then
                      let uu____16176 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16176
                    else ());
                   (let uu____16178 = encode_formula q1 env1 in
                    match uu____16178 with
                    | (phi,qdecls) ->
                        let uu____16190 =
                          let uu____16193 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16193 phi in
                        (match uu____16190 with
                         | (labels,phi1) ->
                             let uu____16203 = encode_labels labels in
                             (match uu____16203 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____16224 =
                                      let uu____16228 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16229 =
                                        varops.mk_unique "@query" in
                                      (uu____16228, (Some "query"),
                                        uu____16229) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16224 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16242 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16242 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16244 = encode_formula q env in
       match uu____16244 with
       | (f,uu____16248) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16250) -> true
             | uu____16253 -> false)))