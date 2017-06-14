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
    let uu___127_803 = x in
    let uu____804 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____804;
      FStar_Syntax_Syntax.index = (uu___127_803.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___127_803.FStar_Syntax_Syntax.sort)
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
        (let uu___128_1118 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___128_1118.tcenv);
           warn = (uu___128_1118.warn);
           cache = (uu___128_1118.cache);
           nolabels = (uu___128_1118.nolabels);
           use_zfuel_name = (uu___128_1118.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_1118.encode_non_total_function_typ);
           current_module_name = (uu___128_1118.current_module_name)
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
        (let uu___129_1131 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___129_1131.depth);
           tcenv = (uu___129_1131.tcenv);
           warn = (uu___129_1131.warn);
           cache = (uu___129_1131.cache);
           nolabels = (uu___129_1131.nolabels);
           use_zfuel_name = (uu___129_1131.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___129_1131.encode_non_total_function_typ);
           current_module_name = (uu___129_1131.current_module_name)
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
          (let uu___130_1147 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___130_1147.depth);
             tcenv = (uu___130_1147.tcenv);
             warn = (uu___130_1147.warn);
             cache = (uu___130_1147.cache);
             nolabels = (uu___130_1147.nolabels);
             use_zfuel_name = (uu___130_1147.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___130_1147.encode_non_total_function_typ);
             current_module_name = (uu___130_1147.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___131_1157 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___131_1157.depth);
          tcenv = (uu___131_1157.tcenv);
          warn = (uu___131_1157.warn);
          cache = (uu___131_1157.cache);
          nolabels = (uu___131_1157.nolabels);
          use_zfuel_name = (uu___131_1157.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_1157.encode_non_total_function_typ);
          current_module_name = (uu___131_1157.current_module_name)
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
        let uu___132_1220 = env in
        let uu____1221 =
          let uu____1223 =
            let uu____1224 =
              let uu____1231 =
                let uu____1233 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1233 in
              (x, fname, uu____1231, None) in
            Binding_fvar uu____1224 in
          uu____1223 :: (env.bindings) in
        {
          bindings = uu____1221;
          depth = (uu___132_1220.depth);
          tcenv = (uu___132_1220.tcenv);
          warn = (uu___132_1220.warn);
          cache = (uu___132_1220.cache);
          nolabels = (uu___132_1220.nolabels);
          use_zfuel_name = (uu___132_1220.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___132_1220.encode_non_total_function_typ);
          current_module_name = (uu___132_1220.current_module_name)
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
          let uu___133_1363 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___133_1363.depth);
            tcenv = (uu___133_1363.tcenv);
            warn = (uu___133_1363.warn);
            cache = (uu___133_1363.cache);
            nolabels = (uu___133_1363.nolabels);
            use_zfuel_name = (uu___133_1363.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_1363.encode_non_total_function_typ);
            current_module_name = (uu___133_1363.current_module_name)
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
            let uu___134_1398 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___134_1398.depth);
              tcenv = (uu___134_1398.tcenv);
              warn = (uu___134_1398.warn);
              cache = (uu___134_1398.cache);
              nolabels = (uu___134_1398.nolabels);
              use_zfuel_name = (uu___134_1398.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_1398.encode_non_total_function_typ);
              current_module_name = (uu___134_1398.current_module_name)
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
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1447
                         else Some t
                     | uu____1451 -> Some t)
                | uu____1452 -> None))
let lookup_free_var:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____1462 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____1462 with
      | Some t -> t
      | None  ->
          let uu____1465 =
            let uu____1466 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____1466 in
          failwith uu____1465
let lookup_free_var_name:
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____1475 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____1475 with | (x,uu____1482,uu____1483) -> x
let lookup_free_var_sym:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op* FStar_SMTEncoding_Term.term Prims.list)
  =
  fun env  ->
    fun a  ->
      let uu____1499 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____1499 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____1520;
                 FStar_SMTEncoding_Term.rng = uu____1521;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____1529 ->
               (match sym with
                | None  -> ((FStar_SMTEncoding_Term.Var name), [])
                | Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____1543 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name: env_t -> Prims.string -> FStar_SMTEncoding_Term.term option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___107_1552  ->
           match uu___107_1552 with
           | Binding_fvar (uu____1554,nm',tok,uu____1557) when nm = nm' ->
               tok
           | uu____1562 -> None)
let mkForall_fuel' n1 uu____1579 =
  match uu____1579 with
  | (pats,vars,body) ->
      let fallback uu____1595 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1598 = FStar_Options.unthrottle_inductives () in
      if uu____1598
      then fallback ()
      else
        (let uu____1600 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1600 with
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
                       | uu____1619 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1633 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1633
                     | uu____1635 ->
                         let uu____1636 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1636 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1639 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____1665 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____1673 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____1678 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____1679 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____1690 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____1705 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1707 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1707 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____1717;
             FStar_Syntax_Syntax.pos = uu____1718;
             FStar_Syntax_Syntax.vars = uu____1719;_},uu____1720)
          ->
          let uu____1735 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1735 FStar_Option.isNone
      | uu____1744 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1751 =
        let uu____1752 = FStar_Syntax_Util.un_uinst t in
        uu____1752.FStar_Syntax_Syntax.n in
      match uu____1751 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1755,uu____1756,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___108_1785  ->
                  match uu___108_1785 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1786 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1787,uu____1788,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1815 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1815 FStar_Option.isSome
      | uu____1824 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1831 = head_normal env t in
      if uu____1831
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
    let uu____1842 =
      let uu____1843 = FStar_Syntax_Syntax.null_binder t in [uu____1843] in
    let uu____1844 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1842 uu____1844 None
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
                    let uu____1871 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1871
                | s ->
                    let uu____1874 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1874) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___109_1886  ->
    match uu___109_1886 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1887 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____1915;
                       FStar_SMTEncoding_Term.rng = uu____1916;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1930) ->
              let uu____1935 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1945 -> false) args (FStar_List.rev xs)) in
              if uu____1935 then tok_of_name env f else None
          | (uu____1948,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1951 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1953 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1953)) in
              if uu____1951 then Some t else None
          | uu____1956 -> None in
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
    | uu____2047 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___110_2050  ->
    match uu___110_2050 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2052 =
          let uu____2056 =
            let uu____2058 =
              let uu____2059 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2059 in
            [uu____2058] in
          ("FStar.Char.Char", uu____2056) in
        FStar_SMTEncoding_Util.mkApp uu____2052
    | FStar_Const.Const_int (i,None ) ->
        let uu____2067 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2067
    | FStar_Const.Const_int (i,Some uu____2069) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2078) ->
        let uu____2081 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2081
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2085 =
          let uu____2086 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2086 in
        failwith uu____2085
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2105 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2113 ->
            let uu____2118 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2118
        | uu____2119 ->
            if norm1
            then let uu____2120 = whnf env t1 in aux false uu____2120
            else
              (let uu____2122 =
                 let uu____2123 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2124 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2123 uu____2124 in
               failwith uu____2122) in
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
    | uu____2145 ->
        let uu____2146 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2146)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2174::uu____2175::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Syntax_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2178::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2180 -> false
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
        (let uu____2318 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2318
         then
           let uu____2319 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2319
         else ());
        (let uu____2321 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2357  ->
                   fun b  ->
                     match uu____2357 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2400 =
                           let x = unmangle (fst b) in
                           let uu____2409 = gen_term_var env1 x in
                           match uu____2409 with
                           | (xxsym,xx,env') ->
                               let uu____2423 =
                                 let uu____2426 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2426 env1 xx in
                               (match uu____2423 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2400 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2321 with
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
          let uu____2514 = encode_term t env in
          match uu____2514 with
          | (t1,decls) ->
              let uu____2521 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2521, decls)
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
          let uu____2529 = encode_term t env in
          match uu____2529 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2538 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2538, decls)
               | Some f ->
                   let uu____2540 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2540, decls))
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
        let uu____2546 = encode_args args_e env in
        match uu____2546 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2558 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____2565 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____2565 in
            let binary arg_tms1 =
              let uu____2574 =
                let uu____2575 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____2575 in
              let uu____2576 =
                let uu____2577 =
                  let uu____2578 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2578 in
                FStar_SMTEncoding_Term.unboxInt uu____2577 in
              (uu____2574, uu____2576) in
            let mk_default uu____2583 =
              let uu____2584 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2584 with
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
       | FStar_Syntax_Syntax.Tm_type uu____2905 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2908) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2914 = encode_const c in (uu____2914, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2929 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2929 with
            | (binders1,res) ->
                let uu____2936 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2936
                then
                  let uu____2939 = encode_binders None binders1 env in
                  (match uu____2939 with
                   | (vars,guards,env',decls,uu____2954) ->
                       let fsym =
                         let uu____2964 = varops.fresh "f" in
                         (uu____2964, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2967 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_2971 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_2971.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_2971.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_2971.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_2971.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_2971.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_2971.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_2971.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_2971.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_2971.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_2971.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_2971.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_2971.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_2971.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_2971.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_2971.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_2971.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_2971.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_2971.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_2971.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_2971.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_2971.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_2971.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_2971.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2967 with
                        | (pre_opt,res_t) ->
                            let uu____2978 =
                              encode_term_pred None res_t env' app in
                            (match uu____2978 with
                             | (res_pred,decls') ->
                                 let uu____2985 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2992 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2992, [])
                                   | Some pre ->
                                       let uu____2995 =
                                         encode_formula pre env' in
                                       (match uu____2995 with
                                        | (guard,decls0) ->
                                            let uu____3003 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3003, decls0)) in
                                 (match uu____2985 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3011 =
                                          let uu____3017 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3017) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3011 in
                                      let cvars =
                                        let uu____3027 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3027
                                          (FStar_List.filter
                                             (fun uu____3033  ->
                                                match uu____3033 with
                                                | (x,uu____3037) ->
                                                    x <> (fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3048 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3048 with
                                       | Some cache_entry ->
                                           let uu____3053 =
                                             let uu____3054 =
                                               let uu____3058 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3058) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3054 in
                                           (uu____3053,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____3069 =
                                               let uu____3070 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3070 in
                                             varops.mk_unique uu____3069 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars in
                                           let caption =
                                             let uu____3077 =
                                               FStar_Options.log_queries () in
                                             if uu____3077
                                             then
                                               let uu____3079 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____3079
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3085 =
                                               let uu____3089 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3089) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3085 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3097 =
                                               let uu____3101 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3101, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3097 in
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
                                             let uu____3114 =
                                               let uu____3118 =
                                                 let uu____3119 =
                                                   let uu____3125 =
                                                     let uu____3126 =
                                                       let uu____3129 =
                                                         let uu____3130 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3130 in
                                                       (f_has_t, uu____3129) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3126 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3125) in
                                                 mkForall_fuel uu____3119 in
                                               (uu____3118,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3114 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3143 =
                                               let uu____3147 =
                                                 let uu____3148 =
                                                   let uu____3154 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3154) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3148 in
                                               (uu____3147, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3143 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3168 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3168);
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
                     let uu____3179 =
                       let uu____3183 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3183, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3179 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3192 =
                       let uu____3196 =
                         let uu____3197 =
                           let uu____3203 =
                             let uu____3204 =
                               let uu____3207 =
                                 let uu____3208 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3208 in
                               (f_has_t, uu____3207) in
                             FStar_SMTEncoding_Util.mkImp uu____3204 in
                           ([[f_has_t]], [fsym], uu____3203) in
                         mkForall_fuel uu____3197 in
                       (uu____3196, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3192 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3222 ->
           let uu____3227 =
             let uu____3230 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3230 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3235;
                 FStar_Syntax_Syntax.pos = uu____3236;
                 FStar_Syntax_Syntax.vars = uu____3237;_} ->
                 let uu____3244 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____3244 with
                  | (b,f1) ->
                      let uu____3258 =
                        let uu____3259 = FStar_List.hd b in fst uu____3259 in
                      (uu____3258, f1))
             | uu____3264 -> failwith "impossible" in
           (match uu____3227 with
            | (x,f) ->
                let uu____3271 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3271 with
                 | (base_t,decls) ->
                     let uu____3278 = gen_term_var env x in
                     (match uu____3278 with
                      | (x1,xtm,env') ->
                          let uu____3287 = encode_formula f env' in
                          (match uu____3287 with
                           | (refinement,decls') ->
                               let uu____3294 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3294 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3305 =
                                        let uu____3307 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3311 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3307
                                          uu____3311 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3305 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3327  ->
                                              match uu____3327 with
                                              | (y,uu____3331) ->
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
                                    let uu____3350 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3350 with
                                     | Some cache_entry ->
                                         let uu____3355 =
                                           let uu____3356 =
                                             let uu____3360 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3360) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3356 in
                                         (uu____3355,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3372 =
                                             let uu____3373 =
                                               let uu____3374 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3374 in
                                             Prims.strcat module_name
                                               uu____3373 in
                                           varops.mk_unique uu____3372 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3383 =
                                             let uu____3387 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3387) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3383 in
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
                                           let uu____3397 =
                                             let uu____3401 =
                                               let uu____3402 =
                                                 let uu____3408 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3408) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3402 in
                                             (uu____3401,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3397 in
                                         let t_kinding =
                                           let uu____3418 =
                                             let uu____3422 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3422,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3418 in
                                         let t_interp =
                                           let uu____3432 =
                                             let uu____3436 =
                                               let uu____3437 =
                                                 let uu____3443 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3443) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3437 in
                                             let uu____3455 =
                                               let uu____3457 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3457 in
                                             (uu____3436, uu____3455,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3432 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3462 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3462);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3483 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3483 in
           let uu____3484 = encode_term_pred None k env ttm in
           (match uu____3484 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3492 =
                    let uu____3496 =
                      let uu____3497 =
                        let uu____3498 =
                          let uu____3499 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3499 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3498 in
                      varops.mk_unique uu____3497 in
                    (t_has_k, (Some "Uvar typing"), uu____3496) in
                  FStar_SMTEncoding_Util.mkAssume uu____3492 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3502 ->
           let uu____3512 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3512 with
            | (head1,args_e) ->
                let uu____3540 =
                  let uu____3548 =
                    let uu____3549 = FStar_Syntax_Subst.compress head1 in
                    uu____3549.FStar_Syntax_Syntax.n in
                  (uu____3548, args_e) in
                (match uu____3540 with
                 | uu____3559 when head_redex env head1 ->
                     let uu____3567 = whnf env t in
                     encode_term uu____3567 env
                 | uu____3568 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____3581;
                       FStar_Syntax_Syntax.pos = uu____3582;
                       FStar_Syntax_Syntax.vars = uu____3583;_},uu____3584),uu____3585::
                    (v1,uu____3587)::(v2,uu____3589)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3627 = encode_term v1 env in
                     (match uu____3627 with
                      | (v11,decls1) ->
                          let uu____3634 = encode_term v2 env in
                          (match uu____3634 with
                           | (v21,decls2) ->
                               let uu____3641 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3641,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3644::(v1,uu____3646)::(v2,uu____3648)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3682 = encode_term v1 env in
                     (match uu____3682 with
                      | (v11,decls1) ->
                          let uu____3689 = encode_term v2 env in
                          (match uu____3689 with
                           | (v21,decls2) ->
                               let uu____3696 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3696,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3698) ->
                     let e0 =
                       let uu____3710 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3710 in
                     ((let uu____3716 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3716
                       then
                         let uu____3717 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3717
                       else ());
                      (let e =
                         let uu____3722 =
                           let uu____3723 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3724 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3723
                             uu____3724 in
                         uu____3722 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3733),(arg,uu____3735)::[]) -> encode_term arg env
                 | uu____3753 ->
                     let uu____3761 = encode_args args_e env in
                     (match uu____3761 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3794 = encode_term head1 env in
                            match uu____3794 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3833 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3833 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3875  ->
                                                 fun uu____3876  ->
                                                   match (uu____3875,
                                                           uu____3876)
                                                   with
                                                   | ((bv,uu____3890),
                                                      (a,uu____3892)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3906 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3906
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3911 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3911 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3921 =
                                                   let uu____3925 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3930 =
                                                     let uu____3931 =
                                                       let uu____3932 =
                                                         let uu____3933 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3933 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3932 in
                                                     varops.mk_unique
                                                       uu____3931 in
                                                   (uu____3925,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3930) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3921 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3944 = lookup_free_var_sym env fv in
                            match uu____3944 with
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
                                   FStar_Syntax_Syntax.tk = uu____3965;
                                   FStar_Syntax_Syntax.pos = uu____3966;
                                   FStar_Syntax_Syntax.vars = uu____3967;_},uu____3968)
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____3979;
                                   FStar_Syntax_Syntax.pos = uu____3980;
                                   FStar_Syntax_Syntax.vars = uu____3981;_},uu____3982)
                                ->
                                let uu____3987 =
                                  let uu____3988 =
                                    let uu____3991 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3991
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____3988
                                    FStar_Pervasives.snd in
                                Some uu____3987
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4007 =
                                  let uu____4008 =
                                    let uu____4011 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4011
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4008
                                    FStar_Pervasives.snd in
                                Some uu____4007
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4026,(FStar_Util.Inl t1,uu____4028),uu____4029)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4067,(FStar_Util.Inr c,uu____4069),uu____4070)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4108 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4128 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4128 in
                               let uu____4129 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4129 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4139;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4140;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4141;_},uu____4142)
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
                                     | uu____4160 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4205 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4205 with
            | (bs1,body1,opening) ->
                let fallback uu____4220 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____4225 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4225, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4236 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____4236
                  | FStar_Util.Inr (eff,uu____4238) ->
                      let uu____4244 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____4244 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4289 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___136_4290 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___136_4290.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___136_4290.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___136_4290.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___136_4290.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___136_4290.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___136_4290.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___136_4290.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___136_4290.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___136_4290.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___136_4290.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___136_4290.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___136_4290.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___136_4290.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___136_4290.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___136_4290.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___136_4290.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___136_4290.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___136_4290.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___136_4290.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___136_4290.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___136_4290.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___136_4290.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___136_4290.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4289 FStar_Syntax_Syntax.U_unknown in
                        let uu____4291 =
                          let uu____4292 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4292 in
                        FStar_Util.Inl uu____4291
                    | FStar_Util.Inr (eff_name,uu____4299) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4330 =
                        let uu____4331 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4331 in
                      FStar_All.pipe_right uu____4330
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4343 =
                        let uu____4344 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4344 FStar_Pervasives.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4352 =
                          let uu____4353 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4353 in
                        FStar_All.pipe_right uu____4352
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4357 =
                             let uu____4358 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4358 in
                           FStar_All.pipe_right uu____4357
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4369 =
                         let uu____4370 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4370 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4369);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4385 =
                       (is_impure lc1) &&
                         (let uu____4386 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4386) in
                     if uu____4385
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4391 = encode_binders None bs1 env in
                        match uu____4391 with
                        | (vars,guards,envbody,decls,uu____4406) ->
                            let uu____4413 =
                              let uu____4421 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4421
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4413 with
                             | (lc2,body2) ->
                                 let uu____4446 = encode_term body2 envbody in
                                 (match uu____4446 with
                                  | (body3,decls') ->
                                      let uu____4453 =
                                        let uu____4458 = codomain_eff lc2 in
                                        match uu____4458 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4470 =
                                              encode_term tfun env in
                                            (match uu____4470 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4453 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4489 =
                                               let uu____4495 =
                                                 let uu____4496 =
                                                   let uu____4499 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4499, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4496 in
                                               ([], vars, uu____4495) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4489 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4507 =
                                                   let uu____4509 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4509 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4507 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4520 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4520 with
                                            | Some cache_entry ->
                                                let uu____4525 =
                                                  let uu____4526 =
                                                    let uu____4530 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4530) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4526 in
                                                (uu____4525,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | None  ->
                                                let uu____4536 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4536 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4543 =
                                                         let uu____4544 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4544 =
                                                           cache_size in
                                                       if uu____4543
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
                                                         let uu____4555 =
                                                           let uu____4556 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4556 in
                                                         varops.mk_unique
                                                           uu____4555 in
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
                                                       let uu____4561 =
                                                         let uu____4565 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4565) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4561 in
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
                                                           let uu____4577 =
                                                             let uu____4578 =
                                                               let uu____4582
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4582,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4578 in
                                                           [uu____4577] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4590 =
                                                         let uu____4594 =
                                                           let uu____4595 =
                                                             let uu____4601 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4601) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4595 in
                                                         (uu____4594,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4590 in
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
                                                     ((let uu____4611 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4611);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4613,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4614;
                          FStar_Syntax_Syntax.lbunivs = uu____4615;
                          FStar_Syntax_Syntax.lbtyp = uu____4616;
                          FStar_Syntax_Syntax.lbeff = uu____4617;
                          FStar_Syntax_Syntax.lbdef = uu____4618;_}::uu____4619),uu____4620)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4638;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4640;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4656 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4669 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4669, [decl_e])))
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
              let uu____4709 = encode_term e1 env in
              match uu____4709 with
              | (ee1,decls1) ->
                  let uu____4716 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4716 with
                   | (xs,e21) ->
                       let uu____4730 = FStar_List.hd xs in
                       (match uu____4730 with
                        | (x1,uu____4738) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4740 = encode_body e21 env' in
                            (match uu____4740 with
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
            let uu____4762 =
              let uu____4766 =
                let uu____4767 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4767 in
              gen_term_var env uu____4766 in
            match uu____4762 with
            | (scrsym,scr',env1) ->
                let uu____4777 = encode_term e env1 in
                (match uu____4777 with
                 | (scr,decls) ->
                     let uu____4784 =
                       let encode_branch b uu____4800 =
                         match uu____4800 with
                         | (else_case,decls1) ->
                             let uu____4811 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4811 with
                              | (p,w,br) ->
                                  let uu____4830 = encode_pat env1 p in
                                  (match uu____4830 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____4850  ->
                                                   match uu____4850 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____4855 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____4870 =
                                               encode_term w1 env2 in
                                             (match uu____4870 with
                                              | (w2,decls2) ->
                                                  let uu____4878 =
                                                    let uu____4879 =
                                                      let uu____4882 =
                                                        let uu____4883 =
                                                          let uu____4886 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____4886) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____4883 in
                                                      (guard, uu____4882) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____4879 in
                                                  (uu____4878, decls2)) in
                                       (match uu____4855 with
                                        | (guard1,decls2) ->
                                            let uu____4894 =
                                              encode_br br env2 in
                                            (match uu____4894 with
                                             | (br1,decls3) ->
                                                 let uu____4902 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____4902,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4784 with
                      | (match_tm,decls1) ->
                          let uu____4913 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4913, decls1)))
and encode_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4935 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4935
       then
         let uu____4936 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4936
       else ());
      (let uu____4938 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4938 with
       | (vars,pat_term) ->
           let uu____4948 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4971  ->
                     fun v1  ->
                       match uu____4971 with
                       | (env1,vars1) ->
                           let uu____4999 = gen_term_var env1 v1 in
                           (match uu____4999 with
                            | (xx,uu____5011,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4948 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5056 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5057 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5058 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5064 =
                        let uu____5067 = encode_const c in
                        (scrutinee, uu____5067) in
                      FStar_SMTEncoding_Util.mkEq uu____5064
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5080 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5080 with
                        | (uu____5084,uu____5085::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5087 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5102  ->
                                  match uu____5102 with
                                  | (arg,uu____5107) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5111 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5111)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5129) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5148 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5161 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5181  ->
                                  match uu____5181 with
                                  | (arg,uu____5189) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5193 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5193)) in
                      FStar_All.pipe_right uu____5161 FStar_List.flatten in
                let pat_term1 uu____5209 = encode_term pat_term env1 in
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
      let uu____5216 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5231  ->
                fun uu____5232  ->
                  match (uu____5231, uu____5232) with
                  | ((tms,decls),(t,uu____5252)) ->
                      let uu____5263 = encode_term t env in
                      (match uu____5263 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5216 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5297 = FStar_Syntax_Util.list_elements e in
        match uu____5297 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5312 =
          let uu____5322 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5322 FStar_Syntax_Util.head_and_args in
        match uu____5312 with
        | (head1,args) ->
            let uu____5350 =
              let uu____5358 =
                let uu____5359 = FStar_Syntax_Util.un_uinst head1 in
                uu____5359.FStar_Syntax_Syntax.n in
              (uu____5358, args) in
            (match uu____5350 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5370,uu____5371)::(e,uu____5373)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> e
             | uu____5399 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____5426 =
            let uu____5436 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5436 FStar_Syntax_Util.head_and_args in
          match uu____5426 with
          | (head1,args) ->
              let uu____5465 =
                let uu____5473 =
                  let uu____5474 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5474.FStar_Syntax_Syntax.n in
                (uu____5473, args) in
              (match uu____5465 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5487)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5507 -> None) in
        match elts with
        | t1::[] ->
            let uu____5522 = smt_pat_or1 t1 in
            (match uu____5522 with
             | Some e ->
                 let uu____5535 = list_elements1 e in
                 FStar_All.pipe_right uu____5535
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5546 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5546
                           (FStar_List.map one_pat)))
             | uu____5554 ->
                 let uu____5558 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5558])
        | uu____5574 ->
            let uu____5576 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5576] in
      let uu____5592 =
        let uu____5605 =
          let uu____5606 = FStar_Syntax_Subst.compress t in
          uu____5606.FStar_Syntax_Syntax.n in
        match uu____5605 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5633 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5633 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5662;
                        FStar_Syntax_Syntax.effect_name = uu____5663;
                        FStar_Syntax_Syntax.result_typ = uu____5664;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5666)::(post,uu____5668)::(pats,uu____5670)::[];
                        FStar_Syntax_Syntax.flags = uu____5671;_}
                      ->
                      let uu____5703 = lemma_pats pats in
                      (binders1, pre, post, uu____5703)
                  | uu____5716 -> failwith "impos"))
        | uu____5729 -> failwith "Impos" in
      match uu____5592 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___137_5765 = env in
            {
              bindings = (uu___137_5765.bindings);
              depth = (uu___137_5765.depth);
              tcenv = (uu___137_5765.tcenv);
              warn = (uu___137_5765.warn);
              cache = (uu___137_5765.cache);
              nolabels = (uu___137_5765.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___137_5765.encode_non_total_function_typ);
              current_module_name = (uu___137_5765.current_module_name)
            } in
          let uu____5766 = encode_binders None binders env1 in
          (match uu____5766 with
           | (vars,guards,env2,decls,uu____5781) ->
               let uu____5788 =
                 let uu____5795 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____5817 =
                             let uu____5822 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____5822 FStar_List.unzip in
                           match uu____5817 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____5795 FStar_List.unzip in
               (match uu____5788 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___138_5880 = env2 in
                      {
                        bindings = (uu___138_5880.bindings);
                        depth = (uu___138_5880.depth);
                        tcenv = (uu___138_5880.tcenv);
                        warn = (uu___138_5880.warn);
                        cache = (uu___138_5880.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___138_5880.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___138_5880.encode_non_total_function_typ);
                        current_module_name =
                          (uu___138_5880.current_module_name)
                      } in
                    let uu____5881 =
                      let uu____5884 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____5884 env3 in
                    (match uu____5881 with
                     | (pre1,decls'') ->
                         let uu____5889 =
                           let uu____5892 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____5892 env3 in
                         (match uu____5889 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____5899 =
                                let uu____5900 =
                                  let uu____5906 =
                                    let uu____5907 =
                                      let uu____5910 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____5910, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____5907 in
                                  (pats, vars, uu____5906) in
                                FStar_SMTEncoding_Util.mkForall uu____5900 in
                              (uu____5899, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5923 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5923
        then
          let uu____5924 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5925 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5924 uu____5925
        else () in
      let enc f r l =
        let uu____5952 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5965 = encode_term (fst x) env in
                 match uu____5965 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5952 with
        | (decls,args) ->
            let uu____5982 =
              let uu___139_5983 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_5983.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_5983.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5982, decls) in
      let const_op f r uu____6002 = let uu____6005 = f r in (uu____6005, []) in
      let un_op f l =
        let uu____6021 = FStar_List.hd l in FStar_All.pipe_left f uu____6021 in
      let bin_op f uu___111_6034 =
        match uu___111_6034 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6042 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6069 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6078  ->
                 match uu____6078 with
                 | (t,uu____6086) ->
                     let uu____6087 = encode_formula t env in
                     (match uu____6087 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6069 with
        | (decls,phis) ->
            let uu____6104 =
              let uu___140_6105 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_6105.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_6105.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6104, decls) in
      let eq_op r uu___112_6121 =
        match uu___112_6121 with
        | uu____6124::e1::e2::[] ->
            let uu____6155 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6155 r [e1; e2]
        | uu____6174::uu____6175::e1::e2::[] ->
            let uu____6214 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6214 r [e1; e2]
        | l ->
            let uu____6234 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6234 r l in
      let mk_imp1 r uu___113_6253 =
        match uu___113_6253 with
        | (lhs,uu____6257)::(rhs,uu____6259)::[] ->
            let uu____6280 = encode_formula rhs env in
            (match uu____6280 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6289) ->
                      (l1, decls1)
                  | uu____6292 ->
                      let uu____6293 = encode_formula lhs env in
                      (match uu____6293 with
                       | (l2,decls2) ->
                           let uu____6300 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6300, (FStar_List.append decls1 decls2)))))
        | uu____6302 -> failwith "impossible" in
      let mk_ite r uu___114_6317 =
        match uu___114_6317 with
        | (guard,uu____6321)::(_then,uu____6323)::(_else,uu____6325)::[] ->
            let uu____6354 = encode_formula guard env in
            (match uu____6354 with
             | (g,decls1) ->
                 let uu____6361 = encode_formula _then env in
                 (match uu____6361 with
                  | (t,decls2) ->
                      let uu____6368 = encode_formula _else env in
                      (match uu____6368 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6377 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6396 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6396 in
      let connectives =
        let uu____6408 =
          let uu____6417 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6417) in
        let uu____6430 =
          let uu____6440 =
            let uu____6449 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6449) in
          let uu____6462 =
            let uu____6472 =
              let uu____6482 =
                let uu____6491 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6491) in
              let uu____6504 =
                let uu____6514 =
                  let uu____6524 =
                    let uu____6533 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6533) in
                  [uu____6524;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6514 in
              uu____6482 :: uu____6504 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6472 in
          uu____6440 :: uu____6462 in
        uu____6408 :: uu____6430 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6695 = encode_formula phi' env in
            (match uu____6695 with
             | (phi2,decls) ->
                 let uu____6702 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6702, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6703 ->
            let uu____6708 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6708 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6735 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6735 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6743;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6745;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6761 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6761 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6793::(x,uu____6795)::(t,uu____6797)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6831 = encode_term x env in
                 (match uu____6831 with
                  | (x1,decls) ->
                      let uu____6838 = encode_term t env in
                      (match uu____6838 with
                       | (t1,decls') ->
                           let uu____6845 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6845, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6849)::(msg,uu____6851)::(phi2,uu____6853)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6887 =
                   let uu____6890 =
                     let uu____6891 = FStar_Syntax_Subst.compress r in
                     uu____6891.FStar_Syntax_Syntax.n in
                   let uu____6894 =
                     let uu____6895 = FStar_Syntax_Subst.compress msg in
                     uu____6895.FStar_Syntax_Syntax.n in
                   (uu____6890, uu____6894) in
                 (match uu____6887 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6902))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6918 -> fallback phi2)
             | uu____6921 when head_redex env head2 ->
                 let uu____6929 = whnf env phi1 in
                 encode_formula uu____6929 env
             | uu____6930 ->
                 let uu____6938 = encode_term phi1 env in
                 (match uu____6938 with
                  | (tt,decls) ->
                      let uu____6945 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___141_6946 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___141_6946.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___141_6946.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6945, decls)))
        | uu____6949 ->
            let uu____6950 = encode_term phi1 env in
            (match uu____6950 with
             | (tt,decls) ->
                 let uu____6957 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___142_6958 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___142_6958.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___142_6958.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6957, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6985 = encode_binders None bs env1 in
        match uu____6985 with
        | (vars,guards,env2,decls,uu____7007) ->
            let uu____7014 =
              let uu____7021 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7044 =
                          let uu____7049 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7063  ->
                                    match uu____7063 with
                                    | (t,uu____7069) ->
                                        encode_term t
                                          (let uu___143_7070 = env2 in
                                           {
                                             bindings =
                                               (uu___143_7070.bindings);
                                             depth = (uu___143_7070.depth);
                                             tcenv = (uu___143_7070.tcenv);
                                             warn = (uu___143_7070.warn);
                                             cache = (uu___143_7070.cache);
                                             nolabels =
                                               (uu___143_7070.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___143_7070.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___143_7070.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7049 FStar_List.unzip in
                        match uu____7044 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7021 FStar_List.unzip in
            (match uu____7014 with
             | (pats,decls') ->
                 let uu____7122 = encode_formula body env2 in
                 (match uu____7122 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7141;
                             FStar_SMTEncoding_Term.rng = uu____7142;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7150 -> guards in
                      let uu____7153 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7153, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7187  ->
                   match uu____7187 with
                   | (x,uu____7191) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7197 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7203 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7203) uu____7197 tl1 in
             let uu____7205 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7217  ->
                       match uu____7217 with
                       | (b,uu____7221) ->
                           let uu____7222 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7222)) in
             (match uu____7205 with
              | None  -> ()
              | Some (x,uu____7226) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7236 =
                    let uu____7237 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7237 in
                  FStar_Errors.warn pos uu____7236) in
       let uu____7238 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7238 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7244 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7280  ->
                     match uu____7280 with
                     | (l,uu____7290) -> FStar_Ident.lid_equals op l)) in
           (match uu____7244 with
            | None  -> fallback phi1
            | Some (uu____7313,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7342 = encode_q_body env vars pats body in
             match uu____7342 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7368 =
                     let uu____7374 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7374) in
                   FStar_SMTEncoding_Term.mkForall uu____7368
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7386 = encode_q_body env vars pats body in
             match uu____7386 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7411 =
                   let uu____7412 =
                     let uu____7418 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7418) in
                   FStar_SMTEncoding_Term.mkExists uu____7412
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7411, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7472 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7472 with
  | (asym,a) ->
      let uu____7477 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7477 with
       | (xsym,x) ->
           let uu____7482 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7482 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7512 =
                      let uu____7518 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____7518, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7512 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7533 =
                      let uu____7537 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7537) in
                    FStar_SMTEncoding_Util.mkApp uu____7533 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7545 =
                    let uu____7547 =
                      let uu____7549 =
                        let uu____7551 =
                          let uu____7552 =
                            let uu____7556 =
                              let uu____7557 =
                                let uu____7563 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7563) in
                              FStar_SMTEncoding_Util.mkForall uu____7557 in
                            (uu____7556, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7552 in
                        let uu____7572 =
                          let uu____7574 =
                            let uu____7575 =
                              let uu____7579 =
                                let uu____7580 =
                                  let uu____7586 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7586) in
                                FStar_SMTEncoding_Util.mkForall uu____7580 in
                              (uu____7579,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7575 in
                          [uu____7574] in
                        uu____7551 :: uu____7572 in
                      xtok_decl :: uu____7549 in
                    xname_decl :: uu____7547 in
                  (xtok1, uu____7545) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7635 =
                    let uu____7643 =
                      let uu____7649 =
                        let uu____7650 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7650 in
                      quant axy uu____7649 in
                    (FStar_Syntax_Const.op_Eq, uu____7643) in
                  let uu____7656 =
                    let uu____7665 =
                      let uu____7673 =
                        let uu____7679 =
                          let uu____7680 =
                            let uu____7681 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7681 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7680 in
                        quant axy uu____7679 in
                      (FStar_Syntax_Const.op_notEq, uu____7673) in
                    let uu____7687 =
                      let uu____7696 =
                        let uu____7704 =
                          let uu____7710 =
                            let uu____7711 =
                              let uu____7712 =
                                let uu____7715 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7716 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7715, uu____7716) in
                              FStar_SMTEncoding_Util.mkLT uu____7712 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7711 in
                          quant xy uu____7710 in
                        (FStar_Syntax_Const.op_LT, uu____7704) in
                      let uu____7722 =
                        let uu____7731 =
                          let uu____7739 =
                            let uu____7745 =
                              let uu____7746 =
                                let uu____7747 =
                                  let uu____7750 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7751 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7750, uu____7751) in
                                FStar_SMTEncoding_Util.mkLTE uu____7747 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7746 in
                            quant xy uu____7745 in
                          (FStar_Syntax_Const.op_LTE, uu____7739) in
                        let uu____7757 =
                          let uu____7766 =
                            let uu____7774 =
                              let uu____7780 =
                                let uu____7781 =
                                  let uu____7782 =
                                    let uu____7785 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7786 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7785, uu____7786) in
                                  FStar_SMTEncoding_Util.mkGT uu____7782 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7781 in
                              quant xy uu____7780 in
                            (FStar_Syntax_Const.op_GT, uu____7774) in
                          let uu____7792 =
                            let uu____7801 =
                              let uu____7809 =
                                let uu____7815 =
                                  let uu____7816 =
                                    let uu____7817 =
                                      let uu____7820 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7821 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7820, uu____7821) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7817 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7816 in
                                quant xy uu____7815 in
                              (FStar_Syntax_Const.op_GTE, uu____7809) in
                            let uu____7827 =
                              let uu____7836 =
                                let uu____7844 =
                                  let uu____7850 =
                                    let uu____7851 =
                                      let uu____7852 =
                                        let uu____7855 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7856 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7855, uu____7856) in
                                      FStar_SMTEncoding_Util.mkSub uu____7852 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7851 in
                                  quant xy uu____7850 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7844) in
                              let uu____7862 =
                                let uu____7871 =
                                  let uu____7879 =
                                    let uu____7885 =
                                      let uu____7886 =
                                        let uu____7887 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7887 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7886 in
                                    quant qx uu____7885 in
                                  (FStar_Syntax_Const.op_Minus, uu____7879) in
                                let uu____7893 =
                                  let uu____7902 =
                                    let uu____7910 =
                                      let uu____7916 =
                                        let uu____7917 =
                                          let uu____7918 =
                                            let uu____7921 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7922 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7921, uu____7922) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7918 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7917 in
                                      quant xy uu____7916 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7910) in
                                  let uu____7928 =
                                    let uu____7937 =
                                      let uu____7945 =
                                        let uu____7951 =
                                          let uu____7952 =
                                            let uu____7953 =
                                              let uu____7956 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7957 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7956, uu____7957) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7953 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7952 in
                                        quant xy uu____7951 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7945) in
                                    let uu____7963 =
                                      let uu____7972 =
                                        let uu____7980 =
                                          let uu____7986 =
                                            let uu____7987 =
                                              let uu____7988 =
                                                let uu____7991 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7992 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7991, uu____7992) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7988 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7987 in
                                          quant xy uu____7986 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7980) in
                                      let uu____7998 =
                                        let uu____8007 =
                                          let uu____8015 =
                                            let uu____8021 =
                                              let uu____8022 =
                                                let uu____8023 =
                                                  let uu____8026 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8027 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8026, uu____8027) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8023 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8022 in
                                            quant xy uu____8021 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8015) in
                                        let uu____8033 =
                                          let uu____8042 =
                                            let uu____8050 =
                                              let uu____8056 =
                                                let uu____8057 =
                                                  let uu____8058 =
                                                    let uu____8061 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8062 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8061, uu____8062) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8058 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8057 in
                                              quant xy uu____8056 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8050) in
                                          let uu____8068 =
                                            let uu____8077 =
                                              let uu____8085 =
                                                let uu____8091 =
                                                  let uu____8092 =
                                                    let uu____8093 =
                                                      let uu____8096 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8097 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8096,
                                                        uu____8097) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8093 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8092 in
                                                quant xy uu____8091 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8085) in
                                            let uu____8103 =
                                              let uu____8112 =
                                                let uu____8120 =
                                                  let uu____8126 =
                                                    let uu____8127 =
                                                      let uu____8128 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8128 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8127 in
                                                  quant qx uu____8126 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8120) in
                                              [uu____8112] in
                                            uu____8077 :: uu____8103 in
                                          uu____8042 :: uu____8068 in
                                        uu____8007 :: uu____8033 in
                                      uu____7972 :: uu____7998 in
                                    uu____7937 :: uu____7963 in
                                  uu____7902 :: uu____7928 in
                                uu____7871 :: uu____7893 in
                              uu____7836 :: uu____7862 in
                            uu____7801 :: uu____7827 in
                          uu____7766 :: uu____7792 in
                        uu____7731 :: uu____7757 in
                      uu____7696 :: uu____7722 in
                    uu____7665 :: uu____7687 in
                  uu____7635 :: uu____7656 in
                let mk1 l v1 =
                  let uu____8256 =
                    let uu____8261 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8293  ->
                              match uu____8293 with
                              | (l',uu____8302) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8261
                      (FStar_Option.map
                         (fun uu____8335  ->
                            match uu____8335 with | (uu____8346,b) -> b v1)) in
                  FStar_All.pipe_right uu____8256 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8387  ->
                          match uu____8387 with
                          | (l',uu____8396) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8422 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8422 with
        | (xxsym,xx) ->
            let uu____8427 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8427 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8435 =
                   let uu____8439 =
                     let uu____8440 =
                       let uu____8446 =
                         let uu____8447 =
                           let uu____8450 =
                             let uu____8451 =
                               let uu____8454 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8454) in
                             FStar_SMTEncoding_Util.mkEq uu____8451 in
                           (xx_has_type, uu____8450) in
                         FStar_SMTEncoding_Util.mkImp uu____8447 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8446) in
                     FStar_SMTEncoding_Util.mkForall uu____8440 in
                   let uu____8467 =
                     let uu____8468 =
                       let uu____8469 =
                         let uu____8470 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8470 in
                       Prims.strcat module_name uu____8469 in
                     varops.mk_unique uu____8468 in
                   (uu____8439, (Some "pretyping"), uu____8467) in
                 FStar_SMTEncoding_Util.mkAssume uu____8435)
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
    let uu____8500 =
      let uu____8501 =
        let uu____8505 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8505, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8501 in
    let uu____8507 =
      let uu____8509 =
        let uu____8510 =
          let uu____8514 =
            let uu____8515 =
              let uu____8521 =
                let uu____8522 =
                  let uu____8525 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8525) in
                FStar_SMTEncoding_Util.mkImp uu____8522 in
              ([[typing_pred]], [xx], uu____8521) in
            mkForall_fuel uu____8515 in
          (uu____8514, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8510 in
      [uu____8509] in
    uu____8500 :: uu____8507 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8553 =
      let uu____8554 =
        let uu____8558 =
          let uu____8559 =
            let uu____8565 =
              let uu____8568 =
                let uu____8570 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8570] in
              [uu____8568] in
            let uu____8573 =
              let uu____8574 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8574 tt in
            (uu____8565, [bb], uu____8573) in
          FStar_SMTEncoding_Util.mkForall uu____8559 in
        (uu____8558, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8554 in
    let uu____8585 =
      let uu____8587 =
        let uu____8588 =
          let uu____8592 =
            let uu____8593 =
              let uu____8599 =
                let uu____8600 =
                  let uu____8603 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8603) in
                FStar_SMTEncoding_Util.mkImp uu____8600 in
              ([[typing_pred]], [xx], uu____8599) in
            mkForall_fuel uu____8593 in
          (uu____8592, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8588 in
      [uu____8587] in
    uu____8553 :: uu____8585 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8637 =
        let uu____8638 =
          let uu____8642 =
            let uu____8644 =
              let uu____8646 =
                let uu____8648 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8649 =
                  let uu____8651 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8651] in
                uu____8648 :: uu____8649 in
              tt :: uu____8646 in
            tt :: uu____8644 in
          ("Prims.Precedes", uu____8642) in
        FStar_SMTEncoding_Util.mkApp uu____8638 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8637 in
    let precedes_y_x =
      let uu____8654 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8654 in
    let uu____8656 =
      let uu____8657 =
        let uu____8661 =
          let uu____8662 =
            let uu____8668 =
              let uu____8671 =
                let uu____8673 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8673] in
              [uu____8671] in
            let uu____8676 =
              let uu____8677 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8677 tt in
            (uu____8668, [bb], uu____8676) in
          FStar_SMTEncoding_Util.mkForall uu____8662 in
        (uu____8661, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8657 in
    let uu____8688 =
      let uu____8690 =
        let uu____8691 =
          let uu____8695 =
            let uu____8696 =
              let uu____8702 =
                let uu____8703 =
                  let uu____8706 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8706) in
                FStar_SMTEncoding_Util.mkImp uu____8703 in
              ([[typing_pred]], [xx], uu____8702) in
            mkForall_fuel uu____8696 in
          (uu____8695, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8691 in
      let uu____8719 =
        let uu____8721 =
          let uu____8722 =
            let uu____8726 =
              let uu____8727 =
                let uu____8733 =
                  let uu____8734 =
                    let uu____8737 =
                      let uu____8738 =
                        let uu____8740 =
                          let uu____8742 =
                            let uu____8744 =
                              let uu____8745 =
                                let uu____8748 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8749 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8748, uu____8749) in
                              FStar_SMTEncoding_Util.mkGT uu____8745 in
                            let uu____8750 =
                              let uu____8752 =
                                let uu____8753 =
                                  let uu____8756 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8757 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8756, uu____8757) in
                                FStar_SMTEncoding_Util.mkGTE uu____8753 in
                              let uu____8758 =
                                let uu____8760 =
                                  let uu____8761 =
                                    let uu____8764 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8765 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8764, uu____8765) in
                                  FStar_SMTEncoding_Util.mkLT uu____8761 in
                                [uu____8760] in
                              uu____8752 :: uu____8758 in
                            uu____8744 :: uu____8750 in
                          typing_pred_y :: uu____8742 in
                        typing_pred :: uu____8740 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8738 in
                    (uu____8737, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8734 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8733) in
              mkForall_fuel uu____8727 in
            (uu____8726, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8722 in
        [uu____8721] in
      uu____8690 :: uu____8719 in
    uu____8656 :: uu____8688 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8795 =
      let uu____8796 =
        let uu____8800 =
          let uu____8801 =
            let uu____8807 =
              let uu____8810 =
                let uu____8812 = FStar_SMTEncoding_Term.boxString b in
                [uu____8812] in
              [uu____8810] in
            let uu____8815 =
              let uu____8816 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8816 tt in
            (uu____8807, [bb], uu____8815) in
          FStar_SMTEncoding_Util.mkForall uu____8801 in
        (uu____8800, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8796 in
    let uu____8827 =
      let uu____8829 =
        let uu____8830 =
          let uu____8834 =
            let uu____8835 =
              let uu____8841 =
                let uu____8842 =
                  let uu____8845 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8845) in
                FStar_SMTEncoding_Util.mkImp uu____8842 in
              ([[typing_pred]], [xx], uu____8841) in
            mkForall_fuel uu____8835 in
          (uu____8834, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8830 in
      [uu____8829] in
    uu____8795 :: uu____8827 in
  let mk_ref1 env reft_name uu____8867 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8878 =
        let uu____8882 =
          let uu____8884 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8884] in
        (reft_name, uu____8882) in
      FStar_SMTEncoding_Util.mkApp uu____8878 in
    let refb =
      let uu____8887 =
        let uu____8891 =
          let uu____8893 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8893] in
        (reft_name, uu____8891) in
      FStar_SMTEncoding_Util.mkApp uu____8887 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8897 =
      let uu____8898 =
        let uu____8902 =
          let uu____8903 =
            let uu____8909 =
              let uu____8910 =
                let uu____8913 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8913) in
              FStar_SMTEncoding_Util.mkImp uu____8910 in
            ([[typing_pred]], [xx; aa], uu____8909) in
          mkForall_fuel uu____8903 in
        (uu____8902, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____8898 in
    [uu____8897] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8953 =
      let uu____8954 =
        let uu____8958 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8958, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8954 in
    [uu____8953] in
  let mk_and_interp env conj uu____8969 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8986 =
      let uu____8987 =
        let uu____8991 =
          let uu____8992 =
            let uu____8998 =
              let uu____8999 =
                let uu____9002 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9002, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8999 in
            ([[l_and_a_b]], [aa; bb], uu____8998) in
          FStar_SMTEncoding_Util.mkForall uu____8992 in
        (uu____8991, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8987 in
    [uu____8986] in
  let mk_or_interp env disj uu____9026 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9043 =
      let uu____9044 =
        let uu____9048 =
          let uu____9049 =
            let uu____9055 =
              let uu____9056 =
                let uu____9059 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9059, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9056 in
            ([[l_or_a_b]], [aa; bb], uu____9055) in
          FStar_SMTEncoding_Util.mkForall uu____9049 in
        (uu____9048, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9044 in
    [uu____9043] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9100 =
      let uu____9101 =
        let uu____9105 =
          let uu____9106 =
            let uu____9112 =
              let uu____9113 =
                let uu____9116 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9116, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9113 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9112) in
          FStar_SMTEncoding_Util.mkForall uu____9106 in
        (uu____9105, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9101 in
    [uu____9100] in
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
    let uu____9163 =
      let uu____9164 =
        let uu____9168 =
          let uu____9169 =
            let uu____9175 =
              let uu____9176 =
                let uu____9179 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9179, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9176 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9175) in
          FStar_SMTEncoding_Util.mkForall uu____9169 in
        (uu____9168, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9164 in
    [uu____9163] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9224 =
      let uu____9225 =
        let uu____9229 =
          let uu____9230 =
            let uu____9236 =
              let uu____9237 =
                let uu____9240 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9240, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9237 in
            ([[l_imp_a_b]], [aa; bb], uu____9236) in
          FStar_SMTEncoding_Util.mkForall uu____9230 in
        (uu____9229, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9225 in
    [uu____9224] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9281 =
      let uu____9282 =
        let uu____9286 =
          let uu____9287 =
            let uu____9293 =
              let uu____9294 =
                let uu____9297 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9297, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9294 in
            ([[l_iff_a_b]], [aa; bb], uu____9293) in
          FStar_SMTEncoding_Util.mkForall uu____9287 in
        (uu____9286, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9282 in
    [uu____9281] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9331 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9331 in
    let uu____9333 =
      let uu____9334 =
        let uu____9338 =
          let uu____9339 =
            let uu____9345 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9345) in
          FStar_SMTEncoding_Util.mkForall uu____9339 in
        (uu____9338, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9334 in
    [uu____9333] in
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
      let uu____9385 =
        let uu____9389 =
          let uu____9391 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9391] in
        ("Valid", uu____9389) in
      FStar_SMTEncoding_Util.mkApp uu____9385 in
    let uu____9393 =
      let uu____9394 =
        let uu____9398 =
          let uu____9399 =
            let uu____9405 =
              let uu____9406 =
                let uu____9409 =
                  let uu____9410 =
                    let uu____9416 =
                      let uu____9419 =
                        let uu____9421 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9421] in
                      [uu____9419] in
                    let uu____9424 =
                      let uu____9425 =
                        let uu____9428 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9428, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9425 in
                    (uu____9416, [xx1], uu____9424) in
                  FStar_SMTEncoding_Util.mkForall uu____9410 in
                (uu____9409, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9406 in
            ([[l_forall_a_b]], [aa; bb], uu____9405) in
          FStar_SMTEncoding_Util.mkForall uu____9399 in
        (uu____9398, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9394 in
    [uu____9393] in
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
      let uu____9479 =
        let uu____9483 =
          let uu____9485 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9485] in
        ("Valid", uu____9483) in
      FStar_SMTEncoding_Util.mkApp uu____9479 in
    let uu____9487 =
      let uu____9488 =
        let uu____9492 =
          let uu____9493 =
            let uu____9499 =
              let uu____9500 =
                let uu____9503 =
                  let uu____9504 =
                    let uu____9510 =
                      let uu____9513 =
                        let uu____9515 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9515] in
                      [uu____9513] in
                    let uu____9518 =
                      let uu____9519 =
                        let uu____9522 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9522, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9519 in
                    (uu____9510, [xx1], uu____9518) in
                  FStar_SMTEncoding_Util.mkExists uu____9504 in
                (uu____9503, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9500 in
            ([[l_exists_a_b]], [aa; bb], uu____9499) in
          FStar_SMTEncoding_Util.mkForall uu____9493 in
        (uu____9492, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9488 in
    [uu____9487] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9558 =
      let uu____9559 =
        let uu____9563 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9564 = varops.mk_unique "typing_range_const" in
        (uu____9563, (Some "Range_const typing"), uu____9564) in
      FStar_SMTEncoding_Util.mkAssume uu____9559 in
    [uu____9558] in
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
          let uu____9826 =
            FStar_Util.find_opt
              (fun uu____9844  ->
                 match uu____9844 with
                 | (l,uu____9854) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9826 with
          | None  -> []
          | Some (uu____9876,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9909 = encode_function_type_as_formula t env in
        match uu____9909 with
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
            let uu____9937 =
              (let uu____9938 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____9938) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____9937
            then
              let uu____9942 = new_term_constant_and_tok_from_lid env lid in
              match uu____9942 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____9954 =
                      let uu____9955 = FStar_Syntax_Subst.compress t_norm in
                      uu____9955.FStar_Syntax_Syntax.n in
                    match uu____9954 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9960) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____9977  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____9980 -> [] in
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
              (let uu____9989 = prims.is lid in
               if uu____9989
               then
                 let vname = varops.new_fvar lid in
                 let uu____9994 = prims.mk lid vname in
                 match uu____9994 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10009 =
                    let uu____10015 = curried_arrow_formals_comp t_norm in
                    match uu____10015 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10026 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10026
                          then
                            let uu____10027 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___144_10028 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___144_10028.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___144_10028.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___144_10028.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___144_10028.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___144_10028.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___144_10028.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___144_10028.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___144_10028.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___144_10028.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___144_10028.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___144_10028.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___144_10028.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___144_10028.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___144_10028.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___144_10028.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___144_10028.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___144_10028.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___144_10028.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___144_10028.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___144_10028.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___144_10028.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___144_10028.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___144_10028.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10027
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10035 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10035)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10009 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10062 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10062 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10075 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10099  ->
                                     match uu___115_10099 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10102 =
                                           FStar_Util.prefix vars in
                                         (match uu____10102 with
                                          | (uu____10113,(xxsym,uu____10115))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10125 =
                                                let uu____10126 =
                                                  let uu____10130 =
                                                    let uu____10131 =
                                                      let uu____10137 =
                                                        let uu____10138 =
                                                          let uu____10141 =
                                                            let uu____10142 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10142 in
                                                          (vapp, uu____10141) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10138 in
                                                      ([[vapp]], vars,
                                                        uu____10137) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10131 in
                                                  (uu____10130,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10126 in
                                              [uu____10125])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10153 =
                                           FStar_Util.prefix vars in
                                         (match uu____10153 with
                                          | (uu____10164,(xxsym,uu____10166))
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
                                              let uu____10180 =
                                                let uu____10181 =
                                                  let uu____10185 =
                                                    let uu____10186 =
                                                      let uu____10192 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10192) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10186 in
                                                  (uu____10185,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10181 in
                                              [uu____10180])
                                     | uu____10201 -> [])) in
                           let uu____10202 = encode_binders None formals env1 in
                           (match uu____10202 with
                            | (vars,guards,env',decls1,uu____10218) ->
                                let uu____10225 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10230 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10230, decls1)
                                  | Some p ->
                                      let uu____10232 = encode_formula p env' in
                                      (match uu____10232 with
                                       | (g,ds) ->
                                           let uu____10239 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10239,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10225 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10248 =
                                         let uu____10252 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10252) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10248 in
                                     let uu____10257 =
                                       let vname_decl =
                                         let uu____10262 =
                                           let uu____10268 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10273  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10268,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10262 in
                                       let uu____10278 =
                                         let env2 =
                                           let uu___145_10282 = env1 in
                                           {
                                             bindings =
                                               (uu___145_10282.bindings);
                                             depth = (uu___145_10282.depth);
                                             tcenv = (uu___145_10282.tcenv);
                                             warn = (uu___145_10282.warn);
                                             cache = (uu___145_10282.cache);
                                             nolabels =
                                               (uu___145_10282.nolabels);
                                             use_zfuel_name =
                                               (uu___145_10282.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___145_10282.current_module_name)
                                           } in
                                         let uu____10283 =
                                           let uu____10284 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10284 in
                                         if uu____10283
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10278 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10294::uu____10295 ->
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
                                                   let uu____10318 =
                                                     let uu____10324 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10324) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10318 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10338 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10340 =
                                             match formals with
                                             | [] ->
                                                 let uu____10349 =
                                                   let uu____10350 =
                                                     let uu____10352 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10352 in
                                                   push_free_var env1 lid
                                                     vname uu____10350 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10349)
                                             | uu____10355 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10360 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10360 in
                                                 let name_tok_corr =
                                                   let uu____10362 =
                                                     let uu____10366 =
                                                       let uu____10367 =
                                                         let uu____10373 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10373) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10367 in
                                                     (uu____10366,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10362 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10340 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10257 with
                                      | (decls2,env2) ->
                                          let uu____10397 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10402 =
                                              encode_term res_t1 env' in
                                            match uu____10402 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10410 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10410,
                                                  decls) in
                                          (match uu____10397 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10418 =
                                                   let uu____10422 =
                                                     let uu____10423 =
                                                       let uu____10429 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10429) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10423 in
                                                   (uu____10422,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10418 in
                                               let freshness =
                                                 let uu____10438 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10438
                                                 then
                                                   let uu____10441 =
                                                     let uu____10442 =
                                                       let uu____10448 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
                                                       let uu____10454 =
                                                         varops.next_id () in
                                                       (vname, uu____10448,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10454) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10442 in
                                                   let uu____10456 =
                                                     let uu____10458 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10458] in
                                                   uu____10441 :: uu____10456
                                                 else [] in
                                               let g =
                                                 let uu____10462 =
                                                   let uu____10464 =
                                                     let uu____10466 =
                                                       let uu____10468 =
                                                         let uu____10470 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10470 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10468 in
                                                     FStar_List.append decls3
                                                       uu____10466 in
                                                   FStar_List.append decls2
                                                     uu____10464 in
                                                 FStar_List.append decls11
                                                   uu____10462 in
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
          let uu____10492 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10492 with
          | None  ->
              let uu____10511 = encode_free_var env x t t_norm [] in
              (match uu____10511 with
               | (decls,env1) ->
                   let uu____10526 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10526 with
                    | (n1,x',uu____10541) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10553) -> ((n1, x1), [], env)
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
          let uu____10586 = encode_free_var env lid t tt quals in
          match uu____10586 with
          | (decls,env1) ->
              let uu____10597 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10597
              then
                let uu____10601 =
                  let uu____10603 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10603 in
                (uu____10601, env1)
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
             (fun uu____10631  ->
                fun lb  ->
                  match uu____10631 with
                  | (decls,env1) ->
                      let uu____10643 =
                        let uu____10647 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10647
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10643 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10661 = FStar_Syntax_Util.head_and_args t in
    match uu____10661 with
    | (hd1,args) ->
        let uu____10687 =
          let uu____10688 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10688.FStar_Syntax_Syntax.n in
        (match uu____10687 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10692,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10705 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10720  ->
      fun quals  ->
        match uu____10720 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10769 = FStar_Util.first_N nbinders formals in
              match uu____10769 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10809  ->
                         fun uu____10810  ->
                           match (uu____10809, uu____10810) with
                           | ((formal,uu____10820),(binder,uu____10822)) ->
                               let uu____10827 =
                                 let uu____10832 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10832) in
                               FStar_Syntax_Syntax.NT uu____10827) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10837 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10851  ->
                              match uu____10851 with
                              | (x,i) ->
                                  let uu____10858 =
                                    let uu___146_10859 = x in
                                    let uu____10860 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___146_10859.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___146_10859.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10860
                                    } in
                                  (uu____10858, i))) in
                    FStar_All.pipe_right uu____10837
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10872 =
                      let uu____10874 =
                        let uu____10875 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10875.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10874 in
                    let uu____10879 =
                      let uu____10880 = FStar_Syntax_Subst.compress body in
                      let uu____10881 =
                        let uu____10882 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____10882 in
                      FStar_Syntax_Syntax.extend_app_n uu____10880
                        uu____10881 in
                    uu____10879 uu____10872 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10924 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10924
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___147_10925 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___147_10925.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___147_10925.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___147_10925.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___147_10925.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___147_10925.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___147_10925.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___147_10925.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___147_10925.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___147_10925.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___147_10925.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___147_10925.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___147_10925.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___147_10925.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___147_10925.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___147_10925.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___147_10925.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___147_10925.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___147_10925.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___147_10925.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___147_10925.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___147_10925.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___147_10925.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___147_10925.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____10946 = FStar_Syntax_Util.abs_formals e in
                match uu____10946 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____10995::uu____10996 ->
                         let uu____11004 =
                           let uu____11005 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11005.FStar_Syntax_Syntax.n in
                         (match uu____11004 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11032 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11032 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11058 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11058
                                   then
                                     let uu____11076 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11076 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11122  ->
                                                   fun uu____11123  ->
                                                     match (uu____11122,
                                                             uu____11123)
                                                     with
                                                     | ((x,uu____11133),
                                                        (b,uu____11135)) ->
                                                         let uu____11140 =
                                                           let uu____11145 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11145) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11140)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11147 =
                                            let uu____11158 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11158) in
                                          (uu____11147, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11193 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11193 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11245) ->
                              let uu____11250 =
                                let uu____11261 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____11261 in
                              (uu____11250, true)
                          | uu____11294 when Prims.op_Negation norm1 ->
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
                          | uu____11296 ->
                              let uu____11297 =
                                let uu____11298 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11299 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11298
                                  uu____11299 in
                              failwith uu____11297)
                     | uu____11312 ->
                         let uu____11313 =
                           let uu____11314 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11314.FStar_Syntax_Syntax.n in
                         (match uu____11313 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11341 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11341 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11359 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11359 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11407 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11435 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11435
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11442 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11483  ->
                            fun lb  ->
                              match uu____11483 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11534 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11534
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11537 =
                                      let uu____11545 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11545
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11537 with
                                    | (tok,decl,env2) ->
                                        let uu____11570 =
                                          let uu____11577 =
                                            let uu____11583 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11583, tok) in
                                          uu____11577 :: toks in
                                        (uu____11570, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11442 with
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
                        | uu____11685 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11690 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11690 vars)
                            else
                              (let uu____11692 =
                                 let uu____11696 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11696) in
                               FStar_SMTEncoding_Util.mkApp uu____11692) in
                      let uu____11701 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_11703  ->
                                 match uu___116_11703 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11704 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11707 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11707))) in
                      if uu____11701
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11727;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11729;
                                FStar_Syntax_Syntax.lbeff = uu____11730;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11767 =
                                 let uu____11771 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11771 with
                                 | (tcenv',uu____11782,e_t) ->
                                     let uu____11786 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11793 -> failwith "Impossible" in
                                     (match uu____11786 with
                                      | (e1,t_norm1) ->
                                          ((let uu___150_11802 = env1 in
                                            {
                                              bindings =
                                                (uu___150_11802.bindings);
                                              depth = (uu___150_11802.depth);
                                              tcenv = tcenv';
                                              warn = (uu___150_11802.warn);
                                              cache = (uu___150_11802.cache);
                                              nolabels =
                                                (uu___150_11802.nolabels);
                                              use_zfuel_name =
                                                (uu___150_11802.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___150_11802.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___150_11802.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11767 with
                                | (env',e1,t_norm1) ->
                                    let uu____11809 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11809 with
                                     | ((binders,body,uu____11821,uu____11822),curry)
                                         ->
                                         ((let uu____11829 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11829
                                           then
                                             let uu____11830 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11831 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11830 uu____11831
                                           else ());
                                          (let uu____11833 =
                                             encode_binders None binders env' in
                                           match uu____11833 with
                                           | (vars,guards,env'1,binder_decls,uu____11849)
                                               ->
                                               let body1 =
                                                 let uu____11857 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11857
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11860 =
                                                 let uu____11865 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11865
                                                 then
                                                   let uu____11871 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11872 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11871, uu____11872)
                                                 else
                                                   (let uu____11878 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11878)) in
                                               (match uu____11860 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11892 =
                                                        let uu____11896 =
                                                          let uu____11897 =
                                                            let uu____11903 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11903) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11897 in
                                                        let uu____11909 =
                                                          let uu____11911 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11911 in
                                                        (uu____11896,
                                                          uu____11909,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____11892 in
                                                    let uu____11913 =
                                                      let uu____11915 =
                                                        let uu____11917 =
                                                          let uu____11919 =
                                                            let uu____11921 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11921 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11919 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11917 in
                                                      FStar_List.append
                                                        decls1 uu____11915 in
                                                    (uu____11913, env1))))))
                           | uu____11924 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11943 = varops.fresh "fuel" in
                             (uu____11943, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____11946 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____11985  ->
                                     fun uu____11986  ->
                                       match (uu____11985, uu____11986) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12064 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12064 in
                                           let gtok =
                                             let uu____12066 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12066 in
                                           let env3 =
                                             let uu____12068 =
                                               let uu____12070 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12070 in
                                             push_free_var env2 flid gtok
                                               uu____12068 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____11946 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12156
                                 t_norm uu____12158 =
                                 match (uu____12156, uu____12158) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12185;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12186;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12203 =
                                       let uu____12207 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12207 with
                                       | (tcenv',uu____12222,e_t) ->
                                           let uu____12226 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12233 ->
                                                 failwith "Impossible" in
                                           (match uu____12226 with
                                            | (e1,t_norm1) ->
                                                ((let uu___151_12242 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___151_12242.bindings);
                                                    depth =
                                                      (uu___151_12242.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___151_12242.warn);
                                                    cache =
                                                      (uu___151_12242.cache);
                                                    nolabels =
                                                      (uu___151_12242.nolabels);
                                                    use_zfuel_name =
                                                      (uu___151_12242.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___151_12242.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___151_12242.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12203 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12252 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12252
                                            then
                                              let uu____12253 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12254 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12255 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12253 uu____12254
                                                uu____12255
                                            else ());
                                           (let uu____12257 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12257 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12279 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12279
                                                  then
                                                    let uu____12280 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12281 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12282 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12283 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12280 uu____12281
                                                      uu____12282 uu____12283
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12287 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12287 with
                                                  | (vars,guards,env'1,binder_decls,uu____12305)
                                                      ->
                                                      let decl_g =
                                                        let uu____12313 =
                                                          let uu____12319 =
                                                            let uu____12321 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12321 in
                                                          (g, uu____12319,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12313 in
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
                                                        let uu____12336 =
                                                          let uu____12340 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12340) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12336 in
                                                      let gsapp =
                                                        let uu____12346 =
                                                          let uu____12350 =
                                                            let uu____12352 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12352 ::
                                                              vars_tm in
                                                          (g, uu____12350) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12346 in
                                                      let gmax =
                                                        let uu____12356 =
                                                          let uu____12360 =
                                                            let uu____12362 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12362 ::
                                                              vars_tm in
                                                          (g, uu____12360) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12356 in
                                                      let body1 =
                                                        let uu____12366 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12366
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12368 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12368 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12379
                                                               =
                                                               let uu____12383
                                                                 =
                                                                 let uu____12384
                                                                   =
                                                                   let uu____12392
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
                                                                    uu____12392) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12384 in
                                                               let uu____12403
                                                                 =
                                                                 let uu____12405
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12405 in
                                                               (uu____12383,
                                                                 uu____12403,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12379 in
                                                           let eqn_f =
                                                             let uu____12408
                                                               =
                                                               let uu____12412
                                                                 =
                                                                 let uu____12413
                                                                   =
                                                                   let uu____12419
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12419) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12413 in
                                                               (uu____12412,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12408 in
                                                           let eqn_g' =
                                                             let uu____12427
                                                               =
                                                               let uu____12431
                                                                 =
                                                                 let uu____12432
                                                                   =
                                                                   let uu____12438
                                                                    =
                                                                    let uu____12439
                                                                    =
                                                                    let uu____12442
                                                                    =
                                                                    let uu____12443
                                                                    =
                                                                    let uu____12447
                                                                    =
                                                                    let uu____12449
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12449
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12447) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12443 in
                                                                    (gsapp,
                                                                    uu____12442) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12439 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12438) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12432 in
                                                               (uu____12431,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12427 in
                                                           let uu____12461 =
                                                             let uu____12466
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12466
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12483)
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
                                                                    let uu____12498
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12498
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12501
                                                                    =
                                                                    let uu____12505
                                                                    =
                                                                    let uu____12506
                                                                    =
                                                                    let uu____12512
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12512) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12506 in
                                                                    (uu____12505,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12501 in
                                                                 let uu____12523
                                                                   =
                                                                   let uu____12527
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12527
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12535
                                                                    =
                                                                    let uu____12537
                                                                    =
                                                                    let uu____12538
                                                                    =
                                                                    let uu____12542
                                                                    =
                                                                    let uu____12543
                                                                    =
                                                                    let uu____12549
                                                                    =
                                                                    let uu____12550
                                                                    =
                                                                    let uu____12553
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12553,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12550 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12549) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12543 in
                                                                    (uu____12542,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12538 in
                                                                    [uu____12537] in
                                                                    (d3,
                                                                    uu____12535) in
                                                                 (match uu____12523
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12461
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
                               let uu____12588 =
                                 let uu____12595 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12631  ->
                                      fun uu____12632  ->
                                        match (uu____12631, uu____12632) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12718 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12718 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12595 in
                               (match uu____12588 with
                                | (decls2,eqns,env01) ->
                                    let uu____12758 =
                                      let isDeclFun uu___117_12766 =
                                        match uu___117_12766 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12767 -> true
                                        | uu____12773 -> false in
                                      let uu____12774 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12774
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12758 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12801 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12801
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
        let uu____12834 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____12834 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____12837 = encode_sigelt' env se in
      match uu____12837 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12847 =
                  let uu____12848 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____12848 in
                [uu____12847]
            | uu____12849 ->
                let uu____12850 =
                  let uu____12852 =
                    let uu____12853 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12853 in
                  uu____12852 :: g in
                let uu____12854 =
                  let uu____12856 =
                    let uu____12857 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12857 in
                  [uu____12856] in
                FStar_List.append uu____12850 uu____12854 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____12867 =
          let uu____12868 = FStar_Syntax_Subst.compress t in
          uu____12868.FStar_Syntax_Syntax.n in
        match uu____12867 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____12872)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____12875 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12878 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____12881 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____12883 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12885 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____12893 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12896 =
            let uu____12897 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12897 Prims.op_Negation in
          if uu____12896
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12917 ->
                   let uu____12918 =
                     let uu____12921 =
                       let uu____12922 =
                         let uu____12937 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12937) in
                       FStar_Syntax_Syntax.Tm_abs uu____12922 in
                     FStar_Syntax_Syntax.mk uu____12921 in
                   uu____12918 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____12990 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____12990 with
               | (aname,atok,env2) ->
                   let uu____13000 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13000 with
                    | (formals,uu____13010) ->
                        let uu____13017 =
                          let uu____13020 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13020 env2 in
                        (match uu____13017 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13028 =
                                 let uu____13029 =
                                   let uu____13035 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13043  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13035,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13029 in
                               [uu____13028;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13050 =
                               let aux uu____13079 uu____13080 =
                                 match (uu____13079, uu____13080) with
                                 | ((bv,uu____13107),(env3,acc_sorts,acc)) ->
                                     let uu____13128 = gen_term_var env3 bv in
                                     (match uu____13128 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13050 with
                              | (uu____13166,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13180 =
                                      let uu____13184 =
                                        let uu____13185 =
                                          let uu____13191 =
                                            let uu____13192 =
                                              let uu____13195 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13195) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13192 in
                                          ([[app]], xs_sorts, uu____13191) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13185 in
                                      (uu____13184, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13180 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13207 =
                                      let uu____13211 =
                                        let uu____13212 =
                                          let uu____13218 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13218) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13212 in
                                      (uu____13211,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13207 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13228 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13228 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13244,uu____13245)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13246 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13246 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13257,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13262 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13264  ->
                      match uu___118_13264 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13265 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13268 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13269 -> false)) in
            Prims.op_Negation uu____13262 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13275 = encode_top_level_val env fv t quals in
             match uu____13275 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13287 =
                   let uu____13289 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13289 in
                 (uu____13287, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____13295 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____13295 with
           | (uu____13300,f1) ->
               let uu____13302 = encode_formula f1 env in
               (match uu____13302 with
                | (f2,decls) ->
                    let g =
                      let uu____13311 =
                        let uu____13312 =
                          let uu____13316 =
                            let uu____13318 =
                              let uu____13319 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____13319 in
                            Some uu____13318 in
                          let uu____13320 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____13316, uu____13320) in
                        FStar_SMTEncoding_Util.mkAssume uu____13312 in
                      [uu____13311] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13324,attrs) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right attrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let uu____13332 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13339 =
                       let uu____13341 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13341.FStar_Syntax_Syntax.fv_name in
                     uu____13339.FStar_Syntax_Syntax.v in
                   let uu____13342 =
                     let uu____13343 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13343 in
                   if uu____13342
                   then
                     let val_decl =
                       let uu___152_13358 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___152_13358.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___152_13358.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13362 = encode_sigelt' env1 val_decl in
                     match uu____13362 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____13332 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13379,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13381;
                          FStar_Syntax_Syntax.lbtyp = uu____13382;
                          FStar_Syntax_Syntax.lbeff = uu____13383;
                          FStar_Syntax_Syntax.lbdef = uu____13384;_}::[]),uu____13385,uu____13386)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13400 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13400 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13419 =
                   let uu____13421 =
                     let uu____13422 =
                       let uu____13426 =
                         let uu____13427 =
                           let uu____13433 =
                             let uu____13434 =
                               let uu____13437 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13437) in
                             FStar_SMTEncoding_Util.mkEq uu____13434 in
                           ([[b2t_x]], [xx], uu____13433) in
                         FStar_SMTEncoding_Util.mkForall uu____13427 in
                       (uu____13426, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13422 in
                   [uu____13421] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13419 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13454,uu____13455,uu____13456)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_13462  ->
                  match uu___119_13462 with
                  | FStar_Syntax_Syntax.Discriminator uu____13463 -> true
                  | uu____13464 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13466,lids,uu____13468) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13475 =
                     let uu____13476 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13476.FStar_Ident.idText in
                   uu____13475 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_13478  ->
                     match uu___120_13478 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13479 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13482,uu____13483)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_13493  ->
                  match uu___121_13493 with
                  | FStar_Syntax_Syntax.Projector uu____13494 -> true
                  | uu____13497 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13500 = try_lookup_free_var env l in
          (match uu____13500 with
           | Some uu____13504 -> ([], env)
           | None  ->
               let se1 =
                 let uu___153_13507 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___153_13507.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___153_13507.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13513,uu____13514) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13526) ->
          let uu____13531 = encode_sigelts env ses in
          (match uu____13531 with
           | (g,env1) ->
               let uu____13541 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_13551  ->
                         match uu___122_13551 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13552;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13553;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13554;_}
                             -> false
                         | uu____13556 -> true)) in
               (match uu____13541 with
                | (g',inversions) ->
                    let uu____13565 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_13575  ->
                              match uu___123_13575 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13576 ->
                                  true
                              | uu____13582 -> false)) in
                    (match uu____13565 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13593,tps,k,uu____13596,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_13606  ->
                    match uu___124_13606 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13607 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13614 = c in
              match uu____13614 with
              | (name,args,uu____13618,uu____13619,uu____13620) ->
                  let uu____13623 =
                    let uu____13624 =
                      let uu____13630 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13637  ->
                                match uu____13637 with
                                | (uu____13641,sort,uu____13643) -> sort)) in
                      (name, uu____13630, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13624 in
                  [uu____13623]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13661 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13664 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13664 FStar_Option.isNone)) in
            if uu____13661
            then []
            else
              (let uu____13681 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13681 with
               | (xxsym,xx) ->
                   let uu____13687 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13698  ->
                             fun l  ->
                               match uu____13698 with
                               | (out,decls) ->
                                   let uu____13710 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13710 with
                                    | (uu____13716,data_t) ->
                                        let uu____13718 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13718 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13747 =
                                                 let uu____13748 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13748.FStar_Syntax_Syntax.n in
                                               match uu____13747 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13756,indices) ->
                                                   indices
                                               | uu____13772 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13784  ->
                                                         match uu____13784
                                                         with
                                                         | (x,uu____13788) ->
                                                             let uu____13789
                                                               =
                                                               let uu____13790
                                                                 =
                                                                 let uu____13794
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13794,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13790 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13789)
                                                    env) in
                                             let uu____13796 =
                                               encode_args indices env1 in
                                             (match uu____13796 with
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
                                                      let uu____13816 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13824
                                                                 =
                                                                 let uu____13827
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13827,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13824)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13816
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13829 =
                                                      let uu____13830 =
                                                        let uu____13833 =
                                                          let uu____13834 =
                                                            let uu____13837 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13837,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13834 in
                                                        (out, uu____13833) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13830 in
                                                    (uu____13829,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13687 with
                    | (data_ax,decls) ->
                        let uu____13845 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13845 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13856 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13856 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13859 =
                                 let uu____13863 =
                                   let uu____13864 =
                                     let uu____13870 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13878 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13870,
                                       uu____13878) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13864 in
                                 let uu____13886 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13863, (Some "inversion axiom"),
                                   uu____13886) in
                               FStar_SMTEncoding_Util.mkAssume uu____13859 in
                             let pattern_guarded_inversion =
                               let uu____13890 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13890
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13898 =
                                   let uu____13899 =
                                     let uu____13903 =
                                       let uu____13904 =
                                         let uu____13910 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13918 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13910, uu____13918) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13904 in
                                     let uu____13926 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13903, (Some "inversion axiom"),
                                       uu____13926) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____13899 in
                                 [uu____13898]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13929 =
            let uu____13937 =
              let uu____13938 = FStar_Syntax_Subst.compress k in
              uu____13938.FStar_Syntax_Syntax.n in
            match uu____13937 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13967 -> (tps, k) in
          (match uu____13929 with
           | (formals,res) ->
               let uu____13982 = FStar_Syntax_Subst.open_term formals res in
               (match uu____13982 with
                | (formals1,res1) ->
                    let uu____13989 = encode_binders None formals1 env in
                    (match uu____13989 with
                     | (vars,guards,env',binder_decls,uu____14004) ->
                         let uu____14011 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14011 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14024 =
                                  let uu____14028 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14028) in
                                FStar_SMTEncoding_Util.mkApp uu____14024 in
                              let uu____14033 =
                                let tname_decl =
                                  let uu____14039 =
                                    let uu____14040 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14055  ->
                                              match uu____14055 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14063 = varops.next_id () in
                                    (tname, uu____14040,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14063, false) in
                                  constructor_or_logic_type_decl uu____14039 in
                                let uu____14068 =
                                  match vars with
                                  | [] ->
                                      let uu____14075 =
                                        let uu____14076 =
                                          let uu____14078 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14078 in
                                        push_free_var env1 t tname
                                          uu____14076 in
                                      ([], uu____14075)
                                  | uu____14082 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14088 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14088 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14097 =
                                          let uu____14101 =
                                            let uu____14102 =
                                              let uu____14110 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14110) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14102 in
                                          (uu____14101,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14097 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14068 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14033 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14133 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14133 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14147 =
                                               let uu____14148 =
                                                 let uu____14152 =
                                                   let uu____14153 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14153 in
                                                 (uu____14152,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14148 in
                                             [uu____14147]
                                           else [] in
                                         let uu____14156 =
                                           let uu____14158 =
                                             let uu____14160 =
                                               let uu____14161 =
                                                 let uu____14165 =
                                                   let uu____14166 =
                                                     let uu____14172 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14172) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14166 in
                                                 (uu____14165, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14161 in
                                             [uu____14160] in
                                           FStar_List.append karr uu____14158 in
                                         FStar_List.append decls1 uu____14156 in
                                   let aux =
                                     let uu____14181 =
                                       let uu____14183 =
                                         inversion_axioms tapp vars in
                                       let uu____14185 =
                                         let uu____14187 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14187] in
                                       FStar_List.append uu____14183
                                         uu____14185 in
                                     FStar_List.append kindingAx uu____14181 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14192,uu____14193,uu____14194,uu____14195,uu____14196)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14201,t,uu____14203,n_tps,uu____14205) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14210 = new_term_constant_and_tok_from_lid env d in
          (match uu____14210 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14221 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14221 with
                | (formals,t_res) ->
                    let uu____14243 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14243 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14252 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14252 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14290 =
                                            mk_term_projector_name d x in
                                          (uu____14290,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14292 =
                                  let uu____14302 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14302, true) in
                                FStar_All.pipe_right uu____14292
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
                              let uu____14324 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14324 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14332::uu____14333 ->
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
                                         let uu____14358 =
                                           let uu____14364 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14364) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14358
                                     | uu____14377 -> tok_typing in
                                   let uu____14382 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14382 with
                                    | (vars',guards',env'',decls_formals,uu____14397)
                                        ->
                                        let uu____14404 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14404 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14423 ->
                                                   let uu____14427 =
                                                     let uu____14428 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14428 in
                                                   [uu____14427] in
                                             let encode_elim uu____14435 =
                                               let uu____14436 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14436 with
                                               | (head1,args) ->
                                                   let uu____14465 =
                                                     let uu____14466 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14466.FStar_Syntax_Syntax.n in
                                                   (match uu____14465 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____14473;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14474;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14475;_},uu____14476)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14482 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14482
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
                                                                 | uu____14508
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14516
                                                                    =
                                                                    let uu____14517
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14517 in
                                                                    if
                                                                    uu____14516
                                                                    then
                                                                    let uu____14524
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14524]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14526
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14539
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14539
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14561
                                                                    =
                                                                    let uu____14565
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14565 in
                                                                    (match uu____14561
                                                                    with
                                                                    | 
                                                                    (uu____14572,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14578
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14578
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14580
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14580
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
                                                             (match uu____14526
                                                              with
                                                              | (uu____14588,arg_vars,elim_eqns_or_guards,uu____14591)
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
                                                                    let uu____14610
                                                                    =
                                                                    let uu____14614
                                                                    =
                                                                    let uu____14615
                                                                    =
                                                                    let uu____14621
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14627
                                                                    =
                                                                    let uu____14628
                                                                    =
                                                                    let uu____14631
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14631) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14628 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14621,
                                                                    uu____14627) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14615 in
                                                                    (uu____14614,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14610 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14644
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14644,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14646
                                                                    =
                                                                    let uu____14650
                                                                    =
                                                                    let uu____14651
                                                                    =
                                                                    let uu____14657
                                                                    =
                                                                    let uu____14660
                                                                    =
                                                                    let uu____14662
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14662] in
                                                                    [uu____14660] in
                                                                    let uu____14665
                                                                    =
                                                                    let uu____14666
                                                                    =
                                                                    let uu____14669
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14670
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14669,
                                                                    uu____14670) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14666 in
                                                                    (uu____14657,
                                                                    [x],
                                                                    uu____14665) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14651 in
                                                                    let uu____14680
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14650,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14680) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14646
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14685
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
                                                                    (let uu____14700
                                                                    =
                                                                    let uu____14701
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14701
                                                                    dapp1 in
                                                                    [uu____14700]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14685
                                                                    FStar_List.flatten in
                                                                    let uu____14705
                                                                    =
                                                                    let uu____14709
                                                                    =
                                                                    let uu____14710
                                                                    =
                                                                    let uu____14716
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14722
                                                                    =
                                                                    let uu____14723
                                                                    =
                                                                    let uu____14726
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14726) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14723 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14716,
                                                                    uu____14722) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14710 in
                                                                    (uu____14709,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14705) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14738 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14738
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
                                                                 | uu____14764
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14772
                                                                    =
                                                                    let uu____14773
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14773 in
                                                                    if
                                                                    uu____14772
                                                                    then
                                                                    let uu____14780
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14780]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14782
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14795
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14795
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14817
                                                                    =
                                                                    let uu____14821
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14821 in
                                                                    (match uu____14817
                                                                    with
                                                                    | 
                                                                    (uu____14828,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14834
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14834
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14836
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14836
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
                                                             (match uu____14782
                                                              with
                                                              | (uu____14844,arg_vars,elim_eqns_or_guards,uu____14847)
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
                                                                    let uu____14866
                                                                    =
                                                                    let uu____14870
                                                                    =
                                                                    let uu____14871
                                                                    =
                                                                    let uu____14877
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14883
                                                                    =
                                                                    let uu____14884
                                                                    =
                                                                    let uu____14887
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14887) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14884 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14877,
                                                                    uu____14883) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14871 in
                                                                    (uu____14870,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14866 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14900
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14900,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14902
                                                                    =
                                                                    let uu____14906
                                                                    =
                                                                    let uu____14907
                                                                    =
                                                                    let uu____14913
                                                                    =
                                                                    let uu____14916
                                                                    =
                                                                    let uu____14918
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14918] in
                                                                    [uu____14916] in
                                                                    let uu____14921
                                                                    =
                                                                    let uu____14922
                                                                    =
                                                                    let uu____14925
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14926
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14925,
                                                                    uu____14926) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14922 in
                                                                    (uu____14913,
                                                                    [x],
                                                                    uu____14921) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14907 in
                                                                    let uu____14936
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14906,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14936) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14902
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14941
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
                                                                    (let uu____14956
                                                                    =
                                                                    let uu____14957
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14957
                                                                    dapp1 in
                                                                    [uu____14956]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14941
                                                                    FStar_List.flatten in
                                                                    let uu____14961
                                                                    =
                                                                    let uu____14965
                                                                    =
                                                                    let uu____14966
                                                                    =
                                                                    let uu____14972
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14978
                                                                    =
                                                                    let uu____14979
                                                                    =
                                                                    let uu____14982
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14982) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14979 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14972,
                                                                    uu____14978) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14966 in
                                                                    (uu____14965,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14961) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14992 ->
                                                        ((let uu____14994 =
                                                            let uu____14995 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14996 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14995
                                                              uu____14996 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14994);
                                                         ([], []))) in
                                             let uu____14999 = encode_elim () in
                                             (match uu____14999 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15011 =
                                                      let uu____15013 =
                                                        let uu____15015 =
                                                          let uu____15017 =
                                                            let uu____15019 =
                                                              let uu____15020
                                                                =
                                                                let uu____15026
                                                                  =
                                                                  let uu____15028
                                                                    =
                                                                    let uu____15029
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15029 in
                                                                  Some
                                                                    uu____15028 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15026) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15020 in
                                                            [uu____15019] in
                                                          let uu____15032 =
                                                            let uu____15034 =
                                                              let uu____15036
                                                                =
                                                                let uu____15038
                                                                  =
                                                                  let uu____15040
                                                                    =
                                                                    let uu____15042
                                                                    =
                                                                    let uu____15044
                                                                    =
                                                                    let uu____15045
                                                                    =
                                                                    let uu____15049
                                                                    =
                                                                    let uu____15050
                                                                    =
                                                                    let uu____15056
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15056) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15050 in
                                                                    (uu____15049,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15045 in
                                                                    let uu____15063
                                                                    =
                                                                    let uu____15065
                                                                    =
                                                                    let uu____15066
                                                                    =
                                                                    let uu____15070
                                                                    =
                                                                    let uu____15071
                                                                    =
                                                                    let uu____15077
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____15083
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15077,
                                                                    uu____15083) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15071 in
                                                                    (uu____15070,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15066 in
                                                                    [uu____15065] in
                                                                    uu____15044
                                                                    ::
                                                                    uu____15063 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15042 in
                                                                  FStar_List.append
                                                                    uu____15040
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15038 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15036 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15034 in
                                                          FStar_List.append
                                                            uu____15017
                                                            uu____15032 in
                                                        FStar_List.append
                                                          decls3 uu____15015 in
                                                      FStar_List.append
                                                        decls2 uu____15013 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15011 in
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
           (fun uu____15104  ->
              fun se  ->
                match uu____15104 with
                | (g,env1) ->
                    let uu____15116 = encode_sigelt env1 se in
                    (match uu____15116 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15152 =
        match uu____15152 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15170 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____15175 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15175
                   then
                     let uu____15176 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15177 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15178 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15176 uu____15177 uu____15178
                   else ());
                  (let uu____15180 = encode_term t1 env1 in
                   match uu____15180 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15190 =
                         let uu____15194 =
                           let uu____15195 =
                             let uu____15196 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15196
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15195 in
                         new_term_constant_from_string env1 x uu____15194 in
                       (match uu____15190 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15207 = FStar_Options.log_queries () in
                              if uu____15207
                              then
                                let uu____15209 =
                                  let uu____15210 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15211 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15212 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15210 uu____15211 uu____15212 in
                                Some uu____15209
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15223,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15232 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15232 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15245,se,uu____15247) ->
                 let uu____15250 = encode_sigelt env1 se in
                 (match uu____15250 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15260,se) ->
                 let uu____15264 = encode_sigelt env1 se in
                 (match uu____15264 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15274 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15274 with | (uu____15286,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15331  ->
            match uu____15331 with
            | (l,uu____15338,uu____15339) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15360  ->
            match uu____15360 with
            | (l,uu____15368,uu____15369) ->
                let uu____15374 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39) (
                    fst l) in
                let uu____15375 =
                  let uu____15377 =
                    let uu____15378 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15378 in
                  [uu____15377] in
                uu____15374 :: uu____15375)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15389 =
      let uu____15391 =
        let uu____15392 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15394 =
          let uu____15395 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15395 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15392;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15394
        } in
      [uu____15391] in
    FStar_ST.write last_env uu____15389
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15405 = FStar_ST.read last_env in
      match uu____15405 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15411 ->
          let uu___154_15413 = e in
          let uu____15414 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___154_15413.bindings);
            depth = (uu___154_15413.depth);
            tcenv;
            warn = (uu___154_15413.warn);
            cache = (uu___154_15413.cache);
            nolabels = (uu___154_15413.nolabels);
            use_zfuel_name = (uu___154_15413.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15413.encode_non_total_function_typ);
            current_module_name = uu____15414
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15418 = FStar_ST.read last_env in
    match uu____15418 with
    | [] -> failwith "Empty env stack"
    | uu____15423::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15431  ->
    let uu____15432 = FStar_ST.read last_env in
    match uu____15432 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___155_15443 = hd1 in
          {
            bindings = (uu___155_15443.bindings);
            depth = (uu___155_15443.depth);
            tcenv = (uu___155_15443.tcenv);
            warn = (uu___155_15443.warn);
            cache = refs;
            nolabels = (uu___155_15443.nolabels);
            use_zfuel_name = (uu___155_15443.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_15443.encode_non_total_function_typ);
            current_module_name = (uu___155_15443.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15449  ->
    let uu____15450 = FStar_ST.read last_env in
    match uu____15450 with
    | [] -> failwith "Popping an empty stack"
    | uu____15455::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15463  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15466  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15469  ->
    let uu____15470 = FStar_ST.read last_env in
    match uu____15470 with
    | hd1::uu____15476::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15482 -> failwith "Impossible"
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
        | (uu____15531::uu____15532,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___156_15536 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___156_15536.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___156_15536.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___156_15536.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15537 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15548 =
        let uu____15550 =
          let uu____15551 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15551 in
        let uu____15552 = open_fact_db_tags env in uu____15550 :: uu____15552 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15548
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
      let uu____15567 = encode_sigelt env se in
      match uu____15567 with
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
        let uu____15592 = FStar_Options.log_queries () in
        if uu____15592
        then
          let uu____15594 =
            let uu____15595 =
              let uu____15596 =
                let uu____15597 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15597 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15596 in
            FStar_SMTEncoding_Term.Caption uu____15595 in
          uu____15594 :: decls
        else decls in
      let env =
        let uu____15604 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15604 tcenv in
      let uu____15605 = encode_top_level_facts env se in
      match uu____15605 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15614 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15614))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15625 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15625
       then
         let uu____15626 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15626
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15647  ->
                 fun se  ->
                   match uu____15647 with
                   | (g,env2) ->
                       let uu____15659 = encode_top_level_facts env2 se in
                       (match uu____15659 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15672 =
         encode_signature
           (let uu___157_15676 = env in
            {
              bindings = (uu___157_15676.bindings);
              depth = (uu___157_15676.depth);
              tcenv = (uu___157_15676.tcenv);
              warn = false;
              cache = (uu___157_15676.cache);
              nolabels = (uu___157_15676.nolabels);
              use_zfuel_name = (uu___157_15676.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___157_15676.encode_non_total_function_typ);
              current_module_name = (uu___157_15676.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15672 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15688 = FStar_Options.log_queries () in
             if uu____15688
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___158_15693 = env1 in
               {
                 bindings = (uu___158_15693.bindings);
                 depth = (uu___158_15693.depth);
                 tcenv = (uu___158_15693.tcenv);
                 warn = true;
                 cache = (uu___158_15693.cache);
                 nolabels = (uu___158_15693.nolabels);
                 use_zfuel_name = (uu___158_15693.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___158_15693.encode_non_total_function_typ);
                 current_module_name = (uu___158_15693.current_module_name)
               });
            (let uu____15695 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15695
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
        (let uu____15730 =
           let uu____15731 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15731.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15730);
        (let env =
           let uu____15733 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15733 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15740 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15761 = aux rest in
                 (match uu____15761 with
                  | (out,rest1) ->
                      let t =
                        let uu____15779 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15779 with
                        | Some uu____15783 ->
                            let uu____15784 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15784
                              x.FStar_Syntax_Syntax.sort
                        | uu____15785 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15788 =
                        let uu____15790 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___159_15791 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___159_15791.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___159_15791.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15790 :: out in
                      (uu____15788, rest1))
             | uu____15794 -> ([], bindings1) in
           let uu____15798 = aux bindings in
           match uu____15798 with
           | (closing,bindings1) ->
               let uu____15812 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15812, bindings1) in
         match uu____15740 with
         | (q1,bindings1) ->
             let uu____15825 =
               let uu____15828 =
                 FStar_List.filter
                   (fun uu___125_15830  ->
                      match uu___125_15830 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15831 ->
                          false
                      | uu____15835 -> true) bindings1 in
               encode_env_bindings env uu____15828 in
             (match uu____15825 with
              | (env_decls,env1) ->
                  ((let uu____15846 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15846
                    then
                      let uu____15847 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15847
                    else ());
                   (let uu____15849 = encode_formula q1 env1 in
                    match uu____15849 with
                    | (phi,qdecls) ->
                        let uu____15861 =
                          let uu____15864 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15864 phi in
                        (match uu____15861 with
                         | (labels,phi1) ->
                             let uu____15874 = encode_labels labels in
                             (match uu____15874 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15895 =
                                      let uu____15899 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15900 =
                                        varops.mk_unique "@query" in
                                      (uu____15899, (Some "query"),
                                        uu____15900) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____15895 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15913 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15913 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15915 = encode_formula q env in
       match uu____15915 with
       | (f,uu____15919) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15921) -> true
             | uu____15924 -> false)))