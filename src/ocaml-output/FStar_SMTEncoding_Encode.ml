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
         (fun uu___103_1039  ->
            match uu___103_1039 with
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
           (fun uu___104_1054  ->
              match uu___104_1054 with
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
          (fun uu___105_1173  ->
             match uu___105_1173 with
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
                FStar_All.pipe_left (fun _0_39  -> Some _0_39) uu____1233 in
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
        (fun uu___106_1255  ->
           match uu___106_1255 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1277 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1289 =
        lookup_binding env
          (fun uu___107_1291  ->
             match uu___107_1291 with
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
        (fun uu___108_1576  ->
           match uu___108_1576 with
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
      | FStar_Syntax_Syntax.Tm_constant uu____1722 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1724 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1724 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____1738;
             FStar_Syntax_Syntax.pos = uu____1739;
             FStar_Syntax_Syntax.vars = uu____1740;_},uu____1741)
          ->
          let uu____1756 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1756 FStar_Option.isNone
      | uu____1769 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1776 =
        let uu____1777 = FStar_Syntax_Util.un_uinst t in
        uu____1777.FStar_Syntax_Syntax.n in
      match uu____1776 with
      | FStar_Syntax_Syntax.Tm_abs (uu____1780,uu____1781,Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Syntax_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___109_1794  ->
                  match uu___109_1794 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1795 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1797 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1797 FStar_Option.isSome
      | uu____1810 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1817 = head_normal env t in
      if uu____1817
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
    let uu____1828 =
      let uu____1829 = FStar_Syntax_Syntax.null_binder t in [uu____1829] in
    let uu____1830 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1828 uu____1830 None
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
                    let uu____1852 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1852
                | s ->
                    let uu____1855 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1855) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___110_1867  ->
    match uu___110_1867 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1868 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____1896;
                       FStar_SMTEncoding_Term.rng = uu____1897;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1911) ->
              let uu____1916 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1926 -> false) args (FStar_List.rev xs)) in
              if uu____1916 then tok_of_name env f else None
          | (uu____1929,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1932 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1934 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1934)) in
              if uu____1932 then Some t else None
          | uu____1937 -> None in
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
    | uu____2028 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___111_2031  ->
    match uu___111_2031 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2033 =
          let uu____2037 =
            let uu____2039 =
              let uu____2040 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2040 in
            [uu____2039] in
          ("FStar.Char.Char", uu____2037) in
        FStar_SMTEncoding_Util.mkApp uu____2033
    | FStar_Const.Const_int (i,None ) ->
        let uu____2048 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2048
    | FStar_Const.Const_int (i,Some uu____2050) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2059) ->
        let uu____2062 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2062
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2066 =
          let uu____2067 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2067 in
        failwith uu____2066
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2086 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2094 ->
            let uu____2099 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2099
        | uu____2100 ->
            if norm1
            then let uu____2101 = whnf env t1 in aux false uu____2101
            else
              (let uu____2103 =
                 let uu____2104 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2105 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2104 uu____2105 in
               failwith uu____2103) in
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
    | uu____2126 ->
        let uu____2127 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2127)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2155::uu____2156::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Syntax_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2159::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2161 -> false
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
        (let uu____2299 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2299
         then
           let uu____2300 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2300
         else ());
        (let uu____2302 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2338  ->
                   fun b  ->
                     match uu____2338 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2381 =
                           let x = unmangle (fst b) in
                           let uu____2390 = gen_term_var env1 x in
                           match uu____2390 with
                           | (xxsym,xx,env') ->
                               let uu____2404 =
                                 let uu____2407 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2407 env1 xx in
                               (match uu____2404 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2381 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2302 with
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
          let uu____2495 = encode_term t env in
          match uu____2495 with
          | (t1,decls) ->
              let uu____2502 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2502, decls)
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
          let uu____2510 = encode_term t env in
          match uu____2510 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2519 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2519, decls)
               | Some f ->
                   let uu____2521 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2521, decls))
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
        let uu____2527 = encode_args args_e env in
        match uu____2527 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2539 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____2546 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____2546 in
            let binary arg_tms1 =
              let uu____2555 =
                let uu____2556 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____2556 in
              let uu____2557 =
                let uu____2558 =
                  let uu____2559 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2559 in
                FStar_SMTEncoding_Term.unboxInt uu____2558 in
              (uu____2555, uu____2557) in
            let mk_default uu____2564 =
              let uu____2565 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2565 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____2610 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2610
              then
                let uu____2611 = let uu____2612 = mk_args ts in op uu____2612 in
                FStar_All.pipe_right uu____2611 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____2635 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____2635
              then
                let uu____2636 = binary ts in
                match uu____2636 with
                | (t1,t2) ->
                    let uu____2641 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____2641
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2644 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____2644
                 then
                   let uu____2645 = op (binary ts) in
                   FStar_All.pipe_right uu____2645
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
            let uu____2735 =
              let uu____2741 =
                FStar_List.tryFind
                  (fun uu____2753  ->
                     match uu____2753 with
                     | (l,uu____2760) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____2741 FStar_Util.must in
            (match uu____2735 with
             | (uu____2785,op) ->
                 let uu____2793 = op arg_tms in (uu____2793, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2800 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2800
       then
         let uu____2801 = FStar_Syntax_Print.tag_of_term t in
         let uu____2802 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2803 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2801 uu____2802
           uu____2803
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2807 ->
           let uu____2822 =
             let uu____2823 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2824 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2825 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2826 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2823
               uu____2824 uu____2825 uu____2826 in
           failwith uu____2822
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2829 =
             let uu____2830 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2831 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2832 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2833 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2830
               uu____2831 uu____2832 uu____2833 in
           failwith uu____2829
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2837 =
             let uu____2838 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2838 in
           failwith uu____2837
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2843) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2873) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2882 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2882, [])
       | FStar_Syntax_Syntax.Tm_type uu____2888 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2891) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2897 = encode_const c in (uu____2897, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2912 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2912 with
            | (binders1,res) ->
                let uu____2919 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2919
                then
                  let uu____2922 = encode_binders None binders1 env in
                  (match uu____2922 with
                   | (vars,guards,env',decls,uu____2937) ->
                       let fsym =
                         let uu____2947 = varops.fresh "f" in
                         (uu____2947, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2950 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_2954 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_2954.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_2954.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_2954.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_2954.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_2954.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_2954.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_2954.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_2954.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_2954.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_2954.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_2954.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_2954.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_2954.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_2954.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_2954.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_2954.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_2954.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_2954.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_2954.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_2954.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_2954.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_2954.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_2954.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___135_2954.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___135_2954.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___135_2954.FStar_TypeChecker_Env.is_native_tactic)
                            }) res in
                       (match uu____2950 with
                        | (pre_opt,res_t) ->
                            let uu____2961 =
                              encode_term_pred None res_t env' app in
                            (match uu____2961 with
                             | (res_pred,decls') ->
                                 let uu____2968 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2975 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2975, [])
                                   | Some pre ->
                                       let uu____2978 =
                                         encode_formula pre env' in
                                       (match uu____2978 with
                                        | (guard,decls0) ->
                                            let uu____2986 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2986, decls0)) in
                                 (match uu____2968 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2994 =
                                          let uu____3000 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3000) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2994 in
                                      let cvars =
                                        let uu____3010 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3010
                                          (FStar_List.filter
                                             (fun uu____3016  ->
                                                match uu____3016 with
                                                | (x,uu____3020) ->
                                                    x <> (fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3031 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3031 with
                                       | Some cache_entry ->
                                           let uu____3036 =
                                             let uu____3037 =
                                               let uu____3041 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3041) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3037 in
                                           (uu____3036,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____3052 =
                                               let uu____3053 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3053 in
                                             varops.mk_unique uu____3052 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars in
                                           let caption =
                                             let uu____3060 =
                                               FStar_Options.log_queries () in
                                             if uu____3060
                                             then
                                               let uu____3062 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____3062
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3068 =
                                               let uu____3072 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3072) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3068 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3080 =
                                               let uu____3084 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3084, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3080 in
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
                                             let uu____3097 =
                                               let uu____3101 =
                                                 let uu____3102 =
                                                   let uu____3108 =
                                                     let uu____3109 =
                                                       let uu____3112 =
                                                         let uu____3113 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3113 in
                                                       (f_has_t, uu____3112) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3109 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3108) in
                                                 mkForall_fuel uu____3102 in
                                               (uu____3101,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3097 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3126 =
                                               let uu____3130 =
                                                 let uu____3131 =
                                                   let uu____3137 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3137) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3131 in
                                               (uu____3130, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3126 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3151 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3151);
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
                     let uu____3162 =
                       let uu____3166 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3166, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3162 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3175 =
                       let uu____3179 =
                         let uu____3180 =
                           let uu____3186 =
                             let uu____3187 =
                               let uu____3190 =
                                 let uu____3191 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3191 in
                               (f_has_t, uu____3190) in
                             FStar_SMTEncoding_Util.mkImp uu____3187 in
                           ([[f_has_t]], [fsym], uu____3186) in
                         mkForall_fuel uu____3180 in
                       (uu____3179, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3175 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3205 ->
           let uu____3210 =
             let uu____3213 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3213 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3218;
                 FStar_Syntax_Syntax.pos = uu____3219;
                 FStar_Syntax_Syntax.vars = uu____3220;_} ->
                 let uu____3227 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____3227 with
                  | (b,f1) ->
                      let uu____3241 =
                        let uu____3242 = FStar_List.hd b in fst uu____3242 in
                      (uu____3241, f1))
             | uu____3247 -> failwith "impossible" in
           (match uu____3210 with
            | (x,f) ->
                let uu____3254 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3254 with
                 | (base_t,decls) ->
                     let uu____3261 = gen_term_var env x in
                     (match uu____3261 with
                      | (x1,xtm,env') ->
                          let uu____3270 = encode_formula f env' in
                          (match uu____3270 with
                           | (refinement,decls') ->
                               let uu____3277 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3277 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3288 =
                                        let uu____3290 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3294 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3290
                                          uu____3294 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3288 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3310  ->
                                              match uu____3310 with
                                              | (y,uu____3314) ->
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
                                    let uu____3333 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3333 with
                                     | Some cache_entry ->
                                         let uu____3338 =
                                           let uu____3339 =
                                             let uu____3343 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3343) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3339 in
                                         (uu____3338,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3355 =
                                             let uu____3356 =
                                               let uu____3357 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3357 in
                                             Prims.strcat module_name
                                               uu____3356 in
                                           varops.mk_unique uu____3355 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3366 =
                                             let uu____3370 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3370) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3366 in
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
                                           let uu____3381 =
                                             let uu____3385 =
                                               let uu____3386 =
                                                 let uu____3392 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3392) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3386 in
                                             (uu____3385,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3381 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____3407 =
                                             let uu____3411 =
                                               let uu____3412 =
                                                 let uu____3418 =
                                                   let uu____3419 =
                                                     let uu____3422 =
                                                       let uu____3423 =
                                                         let uu____3429 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____3429) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____3423 in
                                                     (uu____3422, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____3419 in
                                                 ([[valid_t]], cvars1,
                                                   uu____3418) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3412 in
                                             (uu____3411,
                                               (Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3407 in
                                         let t_kinding =
                                           let uu____3449 =
                                             let uu____3453 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3453,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3449 in
                                         let t_interp =
                                           let uu____3463 =
                                             let uu____3467 =
                                               let uu____3468 =
                                                 let uu____3474 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3474) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3468 in
                                             let uu____3486 =
                                               let uu____3488 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3488 in
                                             (uu____3467, uu____3486,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3463 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3493 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3493);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3510 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3510 in
           let uu____3511 = encode_term_pred None k env ttm in
           (match uu____3511 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3519 =
                    let uu____3523 =
                      let uu____3524 =
                        let uu____3525 =
                          let uu____3526 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3526 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3525 in
                      varops.mk_unique uu____3524 in
                    (t_has_k, (Some "Uvar typing"), uu____3523) in
                  FStar_SMTEncoding_Util.mkAssume uu____3519 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3529 ->
           let uu____3539 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3539 with
            | (head1,args_e) ->
                let uu____3567 =
                  let uu____3575 =
                    let uu____3576 = FStar_Syntax_Subst.compress head1 in
                    uu____3576.FStar_Syntax_Syntax.n in
                  (uu____3575, args_e) in
                (match uu____3567 with
                 | uu____3586 when head_redex env head1 ->
                     let uu____3594 = whnf env t in
                     encode_term uu____3594 env
                 | uu____3595 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____3608;
                       FStar_Syntax_Syntax.pos = uu____3609;
                       FStar_Syntax_Syntax.vars = uu____3610;_},uu____3611),uu____3612::
                    (v1,uu____3614)::(v2,uu____3616)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3654 = encode_term v1 env in
                     (match uu____3654 with
                      | (v11,decls1) ->
                          let uu____3661 = encode_term v2 env in
                          (match uu____3661 with
                           | (v21,decls2) ->
                               let uu____3668 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3668,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3671::(v1,uu____3673)::(v2,uu____3675)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3709 = encode_term v1 env in
                     (match uu____3709 with
                      | (v11,decls1) ->
                          let uu____3716 = encode_term v2 env in
                          (match uu____3716 with
                           | (v21,decls2) ->
                               let uu____3723 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3723,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3725) ->
                     let e0 =
                       let uu____3737 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3737 in
                     ((let uu____3743 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3743
                       then
                         let uu____3744 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3744
                       else ());
                      (let e =
                         let uu____3749 =
                           let uu____3750 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3751 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3750
                             uu____3751 in
                         uu____3749 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3760),(arg,uu____3762)::[]) -> encode_term arg env
                 | uu____3780 ->
                     let uu____3788 = encode_args args_e env in
                     (match uu____3788 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3821 = encode_term head1 env in
                            match uu____3821 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3860 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3860 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3902  ->
                                                 fun uu____3903  ->
                                                   match (uu____3902,
                                                           uu____3903)
                                                   with
                                                   | ((bv,uu____3917),
                                                      (a,uu____3919)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3933 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3933
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3938 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3938 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3948 =
                                                   let uu____3952 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3957 =
                                                     let uu____3958 =
                                                       let uu____3959 =
                                                         let uu____3960 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3960 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3959 in
                                                     varops.mk_unique
                                                       uu____3958 in
                                                   (uu____3952,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3957) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3948 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3977 = lookup_free_var_sym env fv in
                            match uu____3977 with
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
                                   FStar_Syntax_Syntax.tk = uu____4000;
                                   FStar_Syntax_Syntax.pos = uu____4001;
                                   FStar_Syntax_Syntax.vars = uu____4002;_},uu____4003)
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____4014;
                                   FStar_Syntax_Syntax.pos = uu____4015;
                                   FStar_Syntax_Syntax.vars = uu____4016;_},uu____4017)
                                ->
                                let uu____4022 =
                                  let uu____4023 =
                                    let uu____4026 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4026
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4023
                                    FStar_Pervasives.snd in
                                Some uu____4022
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4046 =
                                  let uu____4047 =
                                    let uu____4050 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4050
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4047
                                    FStar_Pervasives.snd in
                                Some uu____4046
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4069,(FStar_Util.Inl t1,uu____4071),uu____4072)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4110,(FStar_Util.Inr c,uu____4112),uu____4113)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4151 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4171 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4171 in
                               let uu____4172 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4172 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4182;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4183;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4184;_},uu____4185)
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
                                     | uu____4209 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4244 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4244 with
            | (bs1,body1,opening) ->
                let fallback uu____4259 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____4264 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4264, [decl]) in
                let is_impure rc =
                  let uu____4270 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____4270 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | None  ->
                        let uu____4279 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4279 FStar_Pervasives.fst
                    | Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Syntax_Const.effect_Tot_lid
                  then
                    let uu____4292 = FStar_Syntax_Syntax.mk_Total res_typ in
                    Some uu____4292
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Syntax_Const.effect_GTot_lid
                    then
                      (let uu____4295 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       Some uu____4295)
                    else None in
                (match lopt with
                 | None  ->
                     ((let uu____4300 =
                         let uu____4301 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4301 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4300);
                      fallback ())
                 | Some rc ->
                     let uu____4303 =
                       (is_impure rc) &&
                         (let uu____4304 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____4304) in
                     if uu____4303
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4309 = encode_binders None bs1 env in
                        match uu____4309 with
                        | (vars,guards,envbody,decls,uu____4324) ->
                            let body2 =
                              FStar_TypeChecker_Util.reify_body env.tcenv
                                body1 in
                            let uu____4332 = encode_term body2 envbody in
                            (match uu____4332 with
                             | (body3,decls') ->
                                 let uu____4339 =
                                   let uu____4344 = codomain_eff rc in
                                   match uu____4344 with
                                   | None  -> (None, [])
                                   | Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____4356 = encode_term tfun env in
                                       (match uu____4356 with
                                        | (t1,decls1) -> ((Some t1), decls1)) in
                                 (match uu____4339 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____4375 =
                                          let uu____4381 =
                                            let uu____4382 =
                                              let uu____4385 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____4385, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____4382 in
                                          ([], vars, uu____4381) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4375 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | None  -> cvars
                                        | Some t1 ->
                                            let uu____4393 =
                                              let uu____4395 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____4395
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____4393 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____4406 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____4406 with
                                       | Some cache_entry ->
                                           let uu____4411 =
                                             let uu____4412 =
                                               let uu____4416 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____4416) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4412 in
                                           (uu____4411,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let uu____4422 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____4422 with
                                            | Some t1 ->
                                                let decls1 =
                                                  let uu____4429 =
                                                    let uu____4430 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____4430 = cache_size in
                                                  if uu____4429
                                                  then []
                                                  else
                                                    FStar_List.append decls
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
                                                    let uu____4441 =
                                                      let uu____4442 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____4442 in
                                                    varops.mk_unique
                                                      uu____4441 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      None) in
                                                let f =
                                                  let uu____4447 =
                                                    let uu____4451 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____4451) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4447 in
                                                let app = mk_Apply f vars in
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
                                                      let uu____4463 =
                                                        let uu____4464 =
                                                          let uu____4468 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____4468,
                                                            (Some a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____4464 in
                                                      [uu____4463] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____4476 =
                                                    let uu____4480 =
                                                      let uu____4481 =
                                                        let uu____4487 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____4487) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____4481 in
                                                    (uu____4480,
                                                      (Some a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____4476 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____4497 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____4497);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4499,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4500;
                          FStar_Syntax_Syntax.lbunivs = uu____4501;
                          FStar_Syntax_Syntax.lbtyp = uu____4502;
                          FStar_Syntax_Syntax.lbeff = uu____4503;
                          FStar_Syntax_Syntax.lbdef = uu____4504;_}::uu____4505),uu____4506)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4524;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4526;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4542 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4555 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4555, [decl_e])))
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
              let uu____4597 = encode_term e1 env in
              match uu____4597 with
              | (ee1,decls1) ->
                  let uu____4604 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4604 with
                   | (xs,e21) ->
                       let uu____4618 = FStar_List.hd xs in
                       (match uu____4618 with
                        | (x1,uu____4626) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4628 = encode_body e21 env' in
                            (match uu____4628 with
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
            let uu____4650 =
              let uu____4654 =
                let uu____4655 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4655 in
              gen_term_var env uu____4654 in
            match uu____4650 with
            | (scrsym,scr',env1) ->
                let uu____4665 = encode_term e env1 in
                (match uu____4665 with
                 | (scr,decls) ->
                     let uu____4672 =
                       let encode_branch b uu____4688 =
                         match uu____4688 with
                         | (else_case,decls1) ->
                             let uu____4699 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4699 with
                              | (p,w,br) ->
                                  let uu____4720 = encode_pat env1 p in
                                  (match uu____4720 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____4740  ->
                                                   match uu____4740 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____4745 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____4760 =
                                               encode_term w1 env2 in
                                             (match uu____4760 with
                                              | (w2,decls2) ->
                                                  let uu____4768 =
                                                    let uu____4769 =
                                                      let uu____4772 =
                                                        let uu____4773 =
                                                          let uu____4776 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____4776) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____4773 in
                                                      (guard, uu____4772) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____4769 in
                                                  (uu____4768, decls2)) in
                                       (match uu____4745 with
                                        | (guard1,decls2) ->
                                            let uu____4784 =
                                              encode_br br env2 in
                                            (match uu____4784 with
                                             | (br1,decls3) ->
                                                 let uu____4792 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____4792,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4672 with
                      | (match_tm,decls1) ->
                          let uu____4803 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4803, decls1)))
and encode_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4825 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4825
       then
         let uu____4826 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4826
       else ());
      (let uu____4828 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4828 with
       | (vars,pat_term) ->
           let uu____4838 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4861  ->
                     fun v1  ->
                       match uu____4861 with
                       | (env1,vars1) ->
                           let uu____4889 = gen_term_var env1 v1 in
                           (match uu____4889 with
                            | (xx,uu____4901,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4838 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____4948 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____4949 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____4950 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4956 =
                        let uu____4959 = encode_const c in
                        (scrutinee, uu____4959) in
                      FStar_SMTEncoding_Util.mkEq uu____4956
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4978 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4978 with
                        | (uu____4982,uu____4983::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4985 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5006  ->
                                  match uu____5006 with
                                  | (arg,uu____5012) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5022 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5022)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5042) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5061 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5076 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5098  ->
                                  match uu____5098 with
                                  | (arg,uu____5107) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5117 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5117)) in
                      FStar_All.pipe_right uu____5076 FStar_List.flatten in
                let pat_term1 uu____5133 = encode_term pat_term env1 in
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
      let uu____5140 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5155  ->
                fun uu____5156  ->
                  match (uu____5155, uu____5156) with
                  | ((tms,decls),(t,uu____5176)) ->
                      let uu____5187 = encode_term t env in
                      (match uu____5187 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5140 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5221 = FStar_Syntax_Util.list_elements e in
        match uu____5221 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5236 =
          let uu____5246 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5246 FStar_Syntax_Util.head_and_args in
        match uu____5236 with
        | (head1,args) ->
            let uu____5274 =
              let uu____5282 =
                let uu____5283 = FStar_Syntax_Util.un_uinst head1 in
                uu____5283.FStar_Syntax_Syntax.n in
              (uu____5282, args) in
            (match uu____5274 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5294,uu____5295)::(e,uu____5297)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> e
             | uu____5323 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____5350 =
            let uu____5360 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5360 FStar_Syntax_Util.head_and_args in
          match uu____5350 with
          | (head1,args) ->
              let uu____5389 =
                let uu____5397 =
                  let uu____5398 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5398.FStar_Syntax_Syntax.n in
                (uu____5397, args) in
              (match uu____5389 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5411)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5431 -> None) in
        match elts with
        | t1::[] ->
            let uu____5446 = smt_pat_or1 t1 in
            (match uu____5446 with
             | Some e ->
                 let uu____5459 = list_elements1 e in
                 FStar_All.pipe_right uu____5459
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5470 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5470
                           (FStar_List.map one_pat)))
             | uu____5478 ->
                 let uu____5482 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5482])
        | uu____5498 ->
            let uu____5500 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5500] in
      let uu____5516 =
        let uu____5529 =
          let uu____5530 = FStar_Syntax_Subst.compress t in
          uu____5530.FStar_Syntax_Syntax.n in
        match uu____5529 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5557 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5557 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5586;
                        FStar_Syntax_Syntax.effect_name = uu____5587;
                        FStar_Syntax_Syntax.result_typ = uu____5588;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5590)::(post,uu____5592)::(pats,uu____5594)::[];
                        FStar_Syntax_Syntax.flags = uu____5595;_}
                      ->
                      let uu____5627 = lemma_pats pats in
                      (binders1, pre, post, uu____5627)
                  | uu____5640 -> failwith "impos"))
        | uu____5653 -> failwith "Impos" in
      match uu____5516 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___136_5689 = env in
            {
              bindings = (uu___136_5689.bindings);
              depth = (uu___136_5689.depth);
              tcenv = (uu___136_5689.tcenv);
              warn = (uu___136_5689.warn);
              cache = (uu___136_5689.cache);
              nolabels = (uu___136_5689.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___136_5689.encode_non_total_function_typ);
              current_module_name = (uu___136_5689.current_module_name)
            } in
          let uu____5690 = encode_binders None binders env1 in
          (match uu____5690 with
           | (vars,guards,env2,decls,uu____5705) ->
               let uu____5712 =
                 let uu____5719 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____5741 =
                             let uu____5746 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____5746 FStar_List.unzip in
                           match uu____5741 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____5719 FStar_List.unzip in
               (match uu____5712 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___137_5804 = env2 in
                      {
                        bindings = (uu___137_5804.bindings);
                        depth = (uu___137_5804.depth);
                        tcenv = (uu___137_5804.tcenv);
                        warn = (uu___137_5804.warn);
                        cache = (uu___137_5804.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___137_5804.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___137_5804.encode_non_total_function_typ);
                        current_module_name =
                          (uu___137_5804.current_module_name)
                      } in
                    let uu____5805 =
                      let uu____5808 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____5808 env3 in
                    (match uu____5805 with
                     | (pre1,decls'') ->
                         let uu____5813 =
                           let uu____5816 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____5816 env3 in
                         (match uu____5813 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____5823 =
                                let uu____5824 =
                                  let uu____5830 =
                                    let uu____5831 =
                                      let uu____5834 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____5834, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____5831 in
                                  (pats, vars, uu____5830) in
                                FStar_SMTEncoding_Util.mkForall uu____5824 in
                              (uu____5823, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5847 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5847
        then
          let uu____5848 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5849 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5848 uu____5849
        else () in
      let enc f r l =
        let uu____5876 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5889 = encode_term (fst x) env in
                 match uu____5889 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5876 with
        | (decls,args) ->
            let uu____5906 =
              let uu___138_5907 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___138_5907.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___138_5907.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5906, decls) in
      let const_op f r uu____5932 = let uu____5941 = f r in (uu____5941, []) in
      let un_op f l =
        let uu____5957 = FStar_List.hd l in FStar_All.pipe_left f uu____5957 in
      let bin_op f uu___112_5970 =
        match uu___112_5970 with
        | t1::t2::[] -> f (t1, t2)
        | uu____5978 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6005 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6014  ->
                 match uu____6014 with
                 | (t,uu____6022) ->
                     let uu____6023 = encode_formula t env in
                     (match uu____6023 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6005 with
        | (decls,phis) ->
            let uu____6040 =
              let uu___139_6041 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6041.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6041.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6040, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____6080  ->
               match uu____6080 with
               | (a,q) ->
                   (match q with
                    | Some (FStar_Syntax_Syntax.Implicit uu____6094) -> false
                    | uu____6095 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____6106 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____6106
        else
          (let uu____6118 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____6118 r rf) in
      let mk_imp1 r uu___113_6137 =
        match uu___113_6137 with
        | (lhs,uu____6141)::(rhs,uu____6143)::[] ->
            let uu____6164 = encode_formula rhs env in
            (match uu____6164 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6173) ->
                      (l1, decls1)
                  | uu____6176 ->
                      let uu____6177 = encode_formula lhs env in
                      (match uu____6177 with
                       | (l2,decls2) ->
                           let uu____6184 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6184, (FStar_List.append decls1 decls2)))))
        | uu____6186 -> failwith "impossible" in
      let mk_ite r uu___114_6201 =
        match uu___114_6201 with
        | (guard,uu____6205)::(_then,uu____6207)::(_else,uu____6209)::[] ->
            let uu____6238 = encode_formula guard env in
            (match uu____6238 with
             | (g,decls1) ->
                 let uu____6245 = encode_formula _then env in
                 (match uu____6245 with
                  | (t,decls2) ->
                      let uu____6252 = encode_formula _else env in
                      (match uu____6252 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6261 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6280 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6280 in
      let connectives =
        let uu____6292 =
          let uu____6301 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6301) in
        let uu____6314 =
          let uu____6324 =
            let uu____6333 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6333) in
          let uu____6346 =
            let uu____6356 =
              let uu____6366 =
                let uu____6375 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6375) in
              let uu____6388 =
                let uu____6398 =
                  let uu____6408 =
                    let uu____6417 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6417) in
                  [uu____6408;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6398 in
              uu____6366 :: uu____6388 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6356 in
          uu____6324 :: uu____6346 in
        uu____6292 :: uu____6314 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6633 = encode_formula phi' env in
            (match uu____6633 with
             | (phi2,decls) ->
                 let uu____6640 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6640, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6641 ->
            let uu____6646 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6646 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6675 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6675 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6683;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6685;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6701 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6701 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6733::(x,uu____6735)::(t,uu____6737)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6771 = encode_term x env in
                 (match uu____6771 with
                  | (x1,decls) ->
                      let uu____6778 = encode_term t env in
                      (match uu____6778 with
                       | (t1,decls') ->
                           let uu____6785 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6785, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6789)::(msg,uu____6791)::(phi2,uu____6793)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6827 =
                   let uu____6830 =
                     let uu____6831 = FStar_Syntax_Subst.compress r in
                     uu____6831.FStar_Syntax_Syntax.n in
                   let uu____6834 =
                     let uu____6835 = FStar_Syntax_Subst.compress msg in
                     uu____6835.FStar_Syntax_Syntax.n in
                   (uu____6830, uu____6834) in
                 (match uu____6827 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6842))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6858 -> fallback phi2)
             | uu____6861 when head_redex env head2 ->
                 let uu____6869 = whnf env phi1 in
                 encode_formula uu____6869 env
             | uu____6870 ->
                 let uu____6878 = encode_term phi1 env in
                 (match uu____6878 with
                  | (tt,decls) ->
                      let uu____6885 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___140_6886 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___140_6886.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___140_6886.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6885, decls)))
        | uu____6889 ->
            let uu____6890 = encode_term phi1 env in
            (match uu____6890 with
             | (tt,decls) ->
                 let uu____6897 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___141_6898 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___141_6898.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___141_6898.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6897, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6925 = encode_binders None bs env1 in
        match uu____6925 with
        | (vars,guards,env2,decls,uu____6947) ->
            let uu____6954 =
              let uu____6961 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____6984 =
                          let uu____6989 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7003  ->
                                    match uu____7003 with
                                    | (t,uu____7009) ->
                                        encode_term t
                                          (let uu___142_7010 = env2 in
                                           {
                                             bindings =
                                               (uu___142_7010.bindings);
                                             depth = (uu___142_7010.depth);
                                             tcenv = (uu___142_7010.tcenv);
                                             warn = (uu___142_7010.warn);
                                             cache = (uu___142_7010.cache);
                                             nolabels =
                                               (uu___142_7010.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___142_7010.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___142_7010.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____6989 FStar_List.unzip in
                        match uu____6984 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____6961 FStar_List.unzip in
            (match uu____6954 with
             | (pats,decls') ->
                 let uu____7062 = encode_formula body env2 in
                 (match uu____7062 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7081;
                             FStar_SMTEncoding_Term.rng = uu____7082;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7090 -> guards in
                      let uu____7093 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7093, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7127  ->
                   match uu____7127 with
                   | (x,uu____7131) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7137 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7143 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7143) uu____7137 tl1 in
             let uu____7145 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7157  ->
                       match uu____7157 with
                       | (b,uu____7161) ->
                           let uu____7162 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7162)) in
             (match uu____7145 with
              | None  -> ()
              | Some (x,uu____7166) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7176 =
                    let uu____7177 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7177 in
                  FStar_Errors.warn pos uu____7176) in
       let uu____7178 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7178 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7184 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7220  ->
                     match uu____7220 with
                     | (l,uu____7230) -> FStar_Ident.lid_equals op l)) in
           (match uu____7184 with
            | None  -> fallback phi1
            | Some (uu____7253,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7282 = encode_q_body env vars pats body in
             match uu____7282 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7308 =
                     let uu____7314 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7314) in
                   FStar_SMTEncoding_Term.mkForall uu____7308
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7326 = encode_q_body env vars pats body in
             match uu____7326 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7351 =
                   let uu____7352 =
                     let uu____7358 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7358) in
                   FStar_SMTEncoding_Term.mkExists uu____7352
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7351, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7412 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7412 with
  | (asym,a) ->
      let uu____7417 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7417 with
       | (xsym,x) ->
           let uu____7422 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7422 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7452 =
                      let uu____7458 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____7458, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7452 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7473 =
                      let uu____7477 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7477) in
                    FStar_SMTEncoding_Util.mkApp uu____7473 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7485 =
                    let uu____7487 =
                      let uu____7489 =
                        let uu____7491 =
                          let uu____7492 =
                            let uu____7496 =
                              let uu____7497 =
                                let uu____7503 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7503) in
                              FStar_SMTEncoding_Util.mkForall uu____7497 in
                            (uu____7496, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7492 in
                        let uu____7512 =
                          let uu____7514 =
                            let uu____7515 =
                              let uu____7519 =
                                let uu____7520 =
                                  let uu____7526 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7526) in
                                FStar_SMTEncoding_Util.mkForall uu____7520 in
                              (uu____7519,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7515 in
                          [uu____7514] in
                        uu____7491 :: uu____7512 in
                      xtok_decl :: uu____7489 in
                    xname_decl :: uu____7487 in
                  (xtok1, uu____7485) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7575 =
                    let uu____7583 =
                      let uu____7589 =
                        let uu____7590 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7590 in
                      quant axy uu____7589 in
                    (FStar_Syntax_Const.op_Eq, uu____7583) in
                  let uu____7596 =
                    let uu____7605 =
                      let uu____7613 =
                        let uu____7619 =
                          let uu____7620 =
                            let uu____7621 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7621 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7620 in
                        quant axy uu____7619 in
                      (FStar_Syntax_Const.op_notEq, uu____7613) in
                    let uu____7627 =
                      let uu____7636 =
                        let uu____7644 =
                          let uu____7650 =
                            let uu____7651 =
                              let uu____7652 =
                                let uu____7655 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7656 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7655, uu____7656) in
                              FStar_SMTEncoding_Util.mkLT uu____7652 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7651 in
                          quant xy uu____7650 in
                        (FStar_Syntax_Const.op_LT, uu____7644) in
                      let uu____7662 =
                        let uu____7671 =
                          let uu____7679 =
                            let uu____7685 =
                              let uu____7686 =
                                let uu____7687 =
                                  let uu____7690 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7691 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7690, uu____7691) in
                                FStar_SMTEncoding_Util.mkLTE uu____7687 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7686 in
                            quant xy uu____7685 in
                          (FStar_Syntax_Const.op_LTE, uu____7679) in
                        let uu____7697 =
                          let uu____7706 =
                            let uu____7714 =
                              let uu____7720 =
                                let uu____7721 =
                                  let uu____7722 =
                                    let uu____7725 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7726 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7725, uu____7726) in
                                  FStar_SMTEncoding_Util.mkGT uu____7722 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7721 in
                              quant xy uu____7720 in
                            (FStar_Syntax_Const.op_GT, uu____7714) in
                          let uu____7732 =
                            let uu____7741 =
                              let uu____7749 =
                                let uu____7755 =
                                  let uu____7756 =
                                    let uu____7757 =
                                      let uu____7760 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7761 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7760, uu____7761) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7757 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7756 in
                                quant xy uu____7755 in
                              (FStar_Syntax_Const.op_GTE, uu____7749) in
                            let uu____7767 =
                              let uu____7776 =
                                let uu____7784 =
                                  let uu____7790 =
                                    let uu____7791 =
                                      let uu____7792 =
                                        let uu____7795 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7796 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7795, uu____7796) in
                                      FStar_SMTEncoding_Util.mkSub uu____7792 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7791 in
                                  quant xy uu____7790 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7784) in
                              let uu____7802 =
                                let uu____7811 =
                                  let uu____7819 =
                                    let uu____7825 =
                                      let uu____7826 =
                                        let uu____7827 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7827 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7826 in
                                    quant qx uu____7825 in
                                  (FStar_Syntax_Const.op_Minus, uu____7819) in
                                let uu____7833 =
                                  let uu____7842 =
                                    let uu____7850 =
                                      let uu____7856 =
                                        let uu____7857 =
                                          let uu____7858 =
                                            let uu____7861 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7862 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7861, uu____7862) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7858 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7857 in
                                      quant xy uu____7856 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7850) in
                                  let uu____7868 =
                                    let uu____7877 =
                                      let uu____7885 =
                                        let uu____7891 =
                                          let uu____7892 =
                                            let uu____7893 =
                                              let uu____7896 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7897 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7896, uu____7897) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7893 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7892 in
                                        quant xy uu____7891 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7885) in
                                    let uu____7903 =
                                      let uu____7912 =
                                        let uu____7920 =
                                          let uu____7926 =
                                            let uu____7927 =
                                              let uu____7928 =
                                                let uu____7931 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7932 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7931, uu____7932) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7928 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7927 in
                                          quant xy uu____7926 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7920) in
                                      let uu____7938 =
                                        let uu____7947 =
                                          let uu____7955 =
                                            let uu____7961 =
                                              let uu____7962 =
                                                let uu____7963 =
                                                  let uu____7966 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____7967 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____7966, uu____7967) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____7963 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____7962 in
                                            quant xy uu____7961 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____7955) in
                                        let uu____7973 =
                                          let uu____7982 =
                                            let uu____7990 =
                                              let uu____7996 =
                                                let uu____7997 =
                                                  let uu____7998 =
                                                    let uu____8001 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8002 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8001, uu____8002) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____7998 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____7997 in
                                              quant xy uu____7996 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____7990) in
                                          let uu____8008 =
                                            let uu____8017 =
                                              let uu____8025 =
                                                let uu____8031 =
                                                  let uu____8032 =
                                                    let uu____8033 =
                                                      let uu____8036 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8037 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8036,
                                                        uu____8037) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8033 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8032 in
                                                quant xy uu____8031 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8025) in
                                            let uu____8043 =
                                              let uu____8052 =
                                                let uu____8060 =
                                                  let uu____8066 =
                                                    let uu____8067 =
                                                      let uu____8068 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8068 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8067 in
                                                  quant qx uu____8066 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8060) in
                                              [uu____8052] in
                                            uu____8017 :: uu____8043 in
                                          uu____7982 :: uu____8008 in
                                        uu____7947 :: uu____7973 in
                                      uu____7912 :: uu____7938 in
                                    uu____7877 :: uu____7903 in
                                  uu____7842 :: uu____7868 in
                                uu____7811 :: uu____7833 in
                              uu____7776 :: uu____7802 in
                            uu____7741 :: uu____7767 in
                          uu____7706 :: uu____7732 in
                        uu____7671 :: uu____7697 in
                      uu____7636 :: uu____7662 in
                    uu____7605 :: uu____7627 in
                  uu____7575 :: uu____7596 in
                let mk1 l v1 =
                  let uu____8196 =
                    let uu____8201 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8233  ->
                              match uu____8233 with
                              | (l',uu____8242) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8201
                      (FStar_Option.map
                         (fun uu____8275  ->
                            match uu____8275 with | (uu____8286,b) -> b v1)) in
                  FStar_All.pipe_right uu____8196 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8327  ->
                          match uu____8327 with
                          | (l',uu____8336) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8362 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8362 with
        | (xxsym,xx) ->
            let uu____8367 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8367 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8375 =
                   let uu____8379 =
                     let uu____8380 =
                       let uu____8386 =
                         let uu____8387 =
                           let uu____8390 =
                             let uu____8391 =
                               let uu____8394 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8394) in
                             FStar_SMTEncoding_Util.mkEq uu____8391 in
                           (xx_has_type, uu____8390) in
                         FStar_SMTEncoding_Util.mkImp uu____8387 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8386) in
                     FStar_SMTEncoding_Util.mkForall uu____8380 in
                   let uu____8407 =
                     let uu____8408 =
                       let uu____8409 =
                         let uu____8410 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8410 in
                       Prims.strcat module_name uu____8409 in
                     varops.mk_unique uu____8408 in
                   (uu____8379, (Some "pretyping"), uu____8407) in
                 FStar_SMTEncoding_Util.mkAssume uu____8375)
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
    let uu____8440 =
      let uu____8441 =
        let uu____8445 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8445, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8441 in
    let uu____8447 =
      let uu____8449 =
        let uu____8450 =
          let uu____8454 =
            let uu____8455 =
              let uu____8461 =
                let uu____8462 =
                  let uu____8465 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8465) in
                FStar_SMTEncoding_Util.mkImp uu____8462 in
              ([[typing_pred]], [xx], uu____8461) in
            mkForall_fuel uu____8455 in
          (uu____8454, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8450 in
      [uu____8449] in
    uu____8440 :: uu____8447 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8493 =
      let uu____8494 =
        let uu____8498 =
          let uu____8499 =
            let uu____8505 =
              let uu____8508 =
                let uu____8510 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8510] in
              [uu____8508] in
            let uu____8513 =
              let uu____8514 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8514 tt in
            (uu____8505, [bb], uu____8513) in
          FStar_SMTEncoding_Util.mkForall uu____8499 in
        (uu____8498, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8494 in
    let uu____8525 =
      let uu____8527 =
        let uu____8528 =
          let uu____8532 =
            let uu____8533 =
              let uu____8539 =
                let uu____8540 =
                  let uu____8543 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8543) in
                FStar_SMTEncoding_Util.mkImp uu____8540 in
              ([[typing_pred]], [xx], uu____8539) in
            mkForall_fuel uu____8533 in
          (uu____8532, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8528 in
      [uu____8527] in
    uu____8493 :: uu____8525 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8577 =
        let uu____8578 =
          let uu____8582 =
            let uu____8584 =
              let uu____8586 =
                let uu____8588 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8589 =
                  let uu____8591 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8591] in
                uu____8588 :: uu____8589 in
              tt :: uu____8586 in
            tt :: uu____8584 in
          ("Prims.Precedes", uu____8582) in
        FStar_SMTEncoding_Util.mkApp uu____8578 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8577 in
    let precedes_y_x =
      let uu____8594 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8594 in
    let uu____8596 =
      let uu____8597 =
        let uu____8601 =
          let uu____8602 =
            let uu____8608 =
              let uu____8611 =
                let uu____8613 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8613] in
              [uu____8611] in
            let uu____8616 =
              let uu____8617 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8617 tt in
            (uu____8608, [bb], uu____8616) in
          FStar_SMTEncoding_Util.mkForall uu____8602 in
        (uu____8601, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8597 in
    let uu____8628 =
      let uu____8630 =
        let uu____8631 =
          let uu____8635 =
            let uu____8636 =
              let uu____8642 =
                let uu____8643 =
                  let uu____8646 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8646) in
                FStar_SMTEncoding_Util.mkImp uu____8643 in
              ([[typing_pred]], [xx], uu____8642) in
            mkForall_fuel uu____8636 in
          (uu____8635, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8631 in
      let uu____8659 =
        let uu____8661 =
          let uu____8662 =
            let uu____8666 =
              let uu____8667 =
                let uu____8673 =
                  let uu____8674 =
                    let uu____8677 =
                      let uu____8678 =
                        let uu____8680 =
                          let uu____8682 =
                            let uu____8684 =
                              let uu____8685 =
                                let uu____8688 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8689 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8688, uu____8689) in
                              FStar_SMTEncoding_Util.mkGT uu____8685 in
                            let uu____8690 =
                              let uu____8692 =
                                let uu____8693 =
                                  let uu____8696 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8697 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8696, uu____8697) in
                                FStar_SMTEncoding_Util.mkGTE uu____8693 in
                              let uu____8698 =
                                let uu____8700 =
                                  let uu____8701 =
                                    let uu____8704 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8705 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8704, uu____8705) in
                                  FStar_SMTEncoding_Util.mkLT uu____8701 in
                                [uu____8700] in
                              uu____8692 :: uu____8698 in
                            uu____8684 :: uu____8690 in
                          typing_pred_y :: uu____8682 in
                        typing_pred :: uu____8680 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8678 in
                    (uu____8677, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8674 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8673) in
              mkForall_fuel uu____8667 in
            (uu____8666, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8662 in
        [uu____8661] in
      uu____8630 :: uu____8659 in
    uu____8596 :: uu____8628 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8735 =
      let uu____8736 =
        let uu____8740 =
          let uu____8741 =
            let uu____8747 =
              let uu____8750 =
                let uu____8752 = FStar_SMTEncoding_Term.boxString b in
                [uu____8752] in
              [uu____8750] in
            let uu____8755 =
              let uu____8756 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8756 tt in
            (uu____8747, [bb], uu____8755) in
          FStar_SMTEncoding_Util.mkForall uu____8741 in
        (uu____8740, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8736 in
    let uu____8767 =
      let uu____8769 =
        let uu____8770 =
          let uu____8774 =
            let uu____8775 =
              let uu____8781 =
                let uu____8782 =
                  let uu____8785 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8785) in
                FStar_SMTEncoding_Util.mkImp uu____8782 in
              ([[typing_pred]], [xx], uu____8781) in
            mkForall_fuel uu____8775 in
          (uu____8774, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8770 in
      [uu____8769] in
    uu____8735 :: uu____8767 in
  let mk_ref1 env reft_name uu____8807 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8818 =
        let uu____8822 =
          let uu____8824 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8824] in
        (reft_name, uu____8822) in
      FStar_SMTEncoding_Util.mkApp uu____8818 in
    let refb =
      let uu____8827 =
        let uu____8831 =
          let uu____8833 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8833] in
        (reft_name, uu____8831) in
      FStar_SMTEncoding_Util.mkApp uu____8827 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8837 =
      let uu____8838 =
        let uu____8842 =
          let uu____8843 =
            let uu____8849 =
              let uu____8850 =
                let uu____8853 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8853) in
              FStar_SMTEncoding_Util.mkImp uu____8850 in
            ([[typing_pred]], [xx; aa], uu____8849) in
          mkForall_fuel uu____8843 in
        (uu____8842, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____8838 in
    [uu____8837] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8893 =
      let uu____8894 =
        let uu____8898 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8898, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8894 in
    [uu____8893] in
  let mk_and_interp env conj uu____8909 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8926 =
      let uu____8927 =
        let uu____8931 =
          let uu____8932 =
            let uu____8938 =
              let uu____8939 =
                let uu____8942 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____8942, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8939 in
            ([[l_and_a_b]], [aa; bb], uu____8938) in
          FStar_SMTEncoding_Util.mkForall uu____8932 in
        (uu____8931, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8927 in
    [uu____8926] in
  let mk_or_interp env disj uu____8966 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8983 =
      let uu____8984 =
        let uu____8988 =
          let uu____8989 =
            let uu____8995 =
              let uu____8996 =
                let uu____8999 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____8999, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8996 in
            ([[l_or_a_b]], [aa; bb], uu____8995) in
          FStar_SMTEncoding_Util.mkForall uu____8989 in
        (uu____8988, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8984 in
    [uu____8983] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9040 =
      let uu____9041 =
        let uu____9045 =
          let uu____9046 =
            let uu____9052 =
              let uu____9053 =
                let uu____9056 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9056, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9053 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9052) in
          FStar_SMTEncoding_Util.mkForall uu____9046 in
        (uu____9045, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9041 in
    [uu____9040] in
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
    let uu____9103 =
      let uu____9104 =
        let uu____9108 =
          let uu____9109 =
            let uu____9115 =
              let uu____9116 =
                let uu____9119 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9119, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9116 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9115) in
          FStar_SMTEncoding_Util.mkForall uu____9109 in
        (uu____9108, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9104 in
    [uu____9103] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9164 =
      let uu____9165 =
        let uu____9169 =
          let uu____9170 =
            let uu____9176 =
              let uu____9177 =
                let uu____9180 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9180, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9177 in
            ([[l_imp_a_b]], [aa; bb], uu____9176) in
          FStar_SMTEncoding_Util.mkForall uu____9170 in
        (uu____9169, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9165 in
    [uu____9164] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9221 =
      let uu____9222 =
        let uu____9226 =
          let uu____9227 =
            let uu____9233 =
              let uu____9234 =
                let uu____9237 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9237, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9234 in
            ([[l_iff_a_b]], [aa; bb], uu____9233) in
          FStar_SMTEncoding_Util.mkForall uu____9227 in
        (uu____9226, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9222 in
    [uu____9221] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9271 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9271 in
    let uu____9273 =
      let uu____9274 =
        let uu____9278 =
          let uu____9279 =
            let uu____9285 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9285) in
          FStar_SMTEncoding_Util.mkForall uu____9279 in
        (uu____9278, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9274 in
    [uu____9273] in
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
      let uu____9325 =
        let uu____9329 =
          let uu____9331 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9331] in
        ("Valid", uu____9329) in
      FStar_SMTEncoding_Util.mkApp uu____9325 in
    let uu____9333 =
      let uu____9334 =
        let uu____9338 =
          let uu____9339 =
            let uu____9345 =
              let uu____9346 =
                let uu____9349 =
                  let uu____9350 =
                    let uu____9356 =
                      let uu____9359 =
                        let uu____9361 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9361] in
                      [uu____9359] in
                    let uu____9364 =
                      let uu____9365 =
                        let uu____9368 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9368, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9365 in
                    (uu____9356, [xx1], uu____9364) in
                  FStar_SMTEncoding_Util.mkForall uu____9350 in
                (uu____9349, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9346 in
            ([[l_forall_a_b]], [aa; bb], uu____9345) in
          FStar_SMTEncoding_Util.mkForall uu____9339 in
        (uu____9338, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9334 in
    [uu____9333] in
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
      let uu____9419 =
        let uu____9423 =
          let uu____9425 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9425] in
        ("Valid", uu____9423) in
      FStar_SMTEncoding_Util.mkApp uu____9419 in
    let uu____9427 =
      let uu____9428 =
        let uu____9432 =
          let uu____9433 =
            let uu____9439 =
              let uu____9440 =
                let uu____9443 =
                  let uu____9444 =
                    let uu____9450 =
                      let uu____9453 =
                        let uu____9455 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9455] in
                      [uu____9453] in
                    let uu____9458 =
                      let uu____9459 =
                        let uu____9462 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9462, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9459 in
                    (uu____9450, [xx1], uu____9458) in
                  FStar_SMTEncoding_Util.mkExists uu____9444 in
                (uu____9443, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9440 in
            ([[l_exists_a_b]], [aa; bb], uu____9439) in
          FStar_SMTEncoding_Util.mkForall uu____9433 in
        (uu____9432, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9428 in
    [uu____9427] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9498 =
      let uu____9499 =
        let uu____9503 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9504 = varops.mk_unique "typing_range_const" in
        (uu____9503, (Some "Range_const typing"), uu____9504) in
      FStar_SMTEncoding_Util.mkAssume uu____9499 in
    [uu____9498] in
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
          let uu____9766 =
            FStar_Util.find_opt
              (fun uu____9784  ->
                 match uu____9784 with
                 | (l,uu____9794) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9766 with
          | None  -> []
          | Some (uu____9816,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9853 = encode_function_type_as_formula t env in
        match uu____9853 with
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
            let uu____9885 =
              (let uu____9886 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____9886) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____9885
            then
              let uu____9890 = new_term_constant_and_tok_from_lid env lid in
              match uu____9890 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____9902 =
                      let uu____9903 = FStar_Syntax_Subst.compress t_norm in
                      uu____9903.FStar_Syntax_Syntax.n in
                    match uu____9902 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9908) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____9925  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____9928 -> [] in
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
              (let uu____9937 = prims.is lid in
               if uu____9937
               then
                 let vname = varops.new_fvar lid in
                 let uu____9942 = prims.mk lid vname in
                 match uu____9942 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____9957 =
                    let uu____9963 = curried_arrow_formals_comp t_norm in
                    match uu____9963 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____9974 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____9974
                          then
                            let uu____9975 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___143_9976 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___143_9976.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___143_9976.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___143_9976.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___143_9976.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___143_9976.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___143_9976.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___143_9976.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___143_9976.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___143_9976.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___143_9976.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___143_9976.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___143_9976.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___143_9976.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___143_9976.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___143_9976.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___143_9976.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___143_9976.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___143_9976.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___143_9976.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___143_9976.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___143_9976.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___143_9976.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___143_9976.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___143_9976.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___143_9976.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___143_9976.FStar_TypeChecker_Env.is_native_tactic)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____9975
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____9983 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____9983)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____9957 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10010 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10010 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10023 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10047  ->
                                     match uu___115_10047 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10050 =
                                           FStar_Util.prefix vars in
                                         (match uu____10050 with
                                          | (uu____10061,(xxsym,uu____10063))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10073 =
                                                let uu____10074 =
                                                  let uu____10078 =
                                                    let uu____10079 =
                                                      let uu____10085 =
                                                        let uu____10086 =
                                                          let uu____10089 =
                                                            let uu____10090 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10090 in
                                                          (vapp, uu____10089) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10086 in
                                                      ([[vapp]], vars,
                                                        uu____10085) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10079 in
                                                  (uu____10078,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10074 in
                                              [uu____10073])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10101 =
                                           FStar_Util.prefix vars in
                                         (match uu____10101 with
                                          | (uu____10112,(xxsym,uu____10114))
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
                                              let uu____10128 =
                                                let uu____10129 =
                                                  let uu____10133 =
                                                    let uu____10134 =
                                                      let uu____10140 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10140) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10134 in
                                                  (uu____10133,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10129 in
                                              [uu____10128])
                                     | uu____10149 -> [])) in
                           let uu____10150 = encode_binders None formals env1 in
                           (match uu____10150 with
                            | (vars,guards,env',decls1,uu____10166) ->
                                let uu____10173 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10178 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10178, decls1)
                                  | Some p ->
                                      let uu____10180 = encode_formula p env' in
                                      (match uu____10180 with
                                       | (g,ds) ->
                                           let uu____10187 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10187,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10173 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10196 =
                                         let uu____10200 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10200) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10196 in
                                     let uu____10205 =
                                       let vname_decl =
                                         let uu____10210 =
                                           let uu____10216 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10221  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10216,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10210 in
                                       let uu____10226 =
                                         let env2 =
                                           let uu___144_10230 = env1 in
                                           {
                                             bindings =
                                               (uu___144_10230.bindings);
                                             depth = (uu___144_10230.depth);
                                             tcenv = (uu___144_10230.tcenv);
                                             warn = (uu___144_10230.warn);
                                             cache = (uu___144_10230.cache);
                                             nolabels =
                                               (uu___144_10230.nolabels);
                                             use_zfuel_name =
                                               (uu___144_10230.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___144_10230.current_module_name)
                                           } in
                                         let uu____10231 =
                                           let uu____10232 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10232 in
                                         if uu____10231
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10226 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10242::uu____10243 ->
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
                                                   let uu____10266 =
                                                     let uu____10272 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10272) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10266 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10286 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10288 =
                                             match formals with
                                             | [] ->
                                                 let uu____10297 =
                                                   let uu____10298 =
                                                     let uu____10300 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_41  ->
                                                          Some _0_41)
                                                       uu____10300 in
                                                   push_free_var env1 lid
                                                     vname uu____10298 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10297)
                                             | uu____10303 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10308 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10308 in
                                                 let name_tok_corr =
                                                   let uu____10310 =
                                                     let uu____10314 =
                                                       let uu____10315 =
                                                         let uu____10321 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10321) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10315 in
                                                     (uu____10314,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10310 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10288 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10205 with
                                      | (decls2,env2) ->
                                          let uu____10345 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10350 =
                                              encode_term res_t1 env' in
                                            match uu____10350 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10358 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10358,
                                                  decls) in
                                          (match uu____10345 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10366 =
                                                   let uu____10370 =
                                                     let uu____10371 =
                                                       let uu____10377 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10377) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10371 in
                                                   (uu____10370,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10366 in
                                               let freshness =
                                                 let uu____10386 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10386
                                                 then
                                                   let uu____10389 =
                                                     let uu____10390 =
                                                       let uu____10396 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
                                                       let uu____10402 =
                                                         varops.next_id () in
                                                       (vname, uu____10396,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10402) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10390 in
                                                   let uu____10404 =
                                                     let uu____10406 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10406] in
                                                   uu____10389 :: uu____10404
                                                 else [] in
                                               let g =
                                                 let uu____10410 =
                                                   let uu____10412 =
                                                     let uu____10414 =
                                                       let uu____10416 =
                                                         let uu____10418 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10418 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10416 in
                                                     FStar_List.append decls3
                                                       uu____10414 in
                                                   FStar_List.append decls2
                                                     uu____10412 in
                                                 FStar_List.append decls11
                                                   uu____10410 in
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
          let uu____10440 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10440 with
          | None  ->
              let uu____10463 = encode_free_var env x t t_norm [] in
              (match uu____10463 with
               | (decls,env1) ->
                   let uu____10478 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10478 with
                    | (n1,x',uu____10497) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10509) -> ((n1, x1), [], env)
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
          let uu____10542 = encode_free_var env lid t tt quals in
          match uu____10542 with
          | (decls,env1) ->
              let uu____10553 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10553
              then
                let uu____10557 =
                  let uu____10559 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10559 in
                (uu____10557, env1)
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
             (fun uu____10587  ->
                fun lb  ->
                  match uu____10587 with
                  | (decls,env1) ->
                      let uu____10599 =
                        let uu____10603 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10603
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10599 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10617 = FStar_Syntax_Util.head_and_args t in
    match uu____10617 with
    | (hd1,args) ->
        let uu____10643 =
          let uu____10644 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10644.FStar_Syntax_Syntax.n in
        (match uu____10643 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10648,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10661 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10676  ->
      fun quals  ->
        match uu____10676 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10725 = FStar_Util.first_N nbinders formals in
              match uu____10725 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10765  ->
                         fun uu____10766  ->
                           match (uu____10765, uu____10766) with
                           | ((formal,uu____10776),(binder,uu____10778)) ->
                               let uu____10783 =
                                 let uu____10788 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10788) in
                               FStar_Syntax_Syntax.NT uu____10783) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10793 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10807  ->
                              match uu____10807 with
                              | (x,i) ->
                                  let uu____10814 =
                                    let uu___145_10815 = x in
                                    let uu____10816 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___145_10815.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___145_10815.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10816
                                    } in
                                  (uu____10814, i))) in
                    FStar_All.pipe_right uu____10793
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10828 =
                      let uu____10830 =
                        let uu____10831 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10831.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_42  -> Some _0_42)
                        uu____10830 in
                    let uu____10835 =
                      let uu____10836 = FStar_Syntax_Subst.compress body in
                      let uu____10837 =
                        let uu____10838 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____10838 in
                      FStar_Syntax_Syntax.extend_app_n uu____10836
                        uu____10837 in
                    uu____10835 uu____10828 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10880 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10880
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___146_10881 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___146_10881.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___146_10881.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___146_10881.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___146_10881.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___146_10881.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___146_10881.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___146_10881.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___146_10881.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___146_10881.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___146_10881.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___146_10881.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___146_10881.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___146_10881.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___146_10881.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___146_10881.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___146_10881.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___146_10881.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___146_10881.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___146_10881.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___146_10881.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___146_10881.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___146_10881.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___146_10881.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___146_10881.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___146_10881.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___146_10881.FStar_TypeChecker_Env.is_native_tactic)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____10902 = FStar_Syntax_Util.abs_formals e in
                match uu____10902 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____10936::uu____10937 ->
                         let uu____10945 =
                           let uu____10946 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____10946.FStar_Syntax_Syntax.n in
                         (match uu____10945 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____10973 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____10973 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____10999 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____10999
                                   then
                                     let uu____11017 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11017 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11063  ->
                                                   fun uu____11064  ->
                                                     match (uu____11063,
                                                             uu____11064)
                                                     with
                                                     | ((x,uu____11074),
                                                        (b,uu____11076)) ->
                                                         let uu____11081 =
                                                           let uu____11086 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11086) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11081)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11088 =
                                            let uu____11099 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11099) in
                                          (uu____11088, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11134 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11134 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11186) ->
                              let uu____11191 =
                                let uu____11202 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____11202 in
                              (uu____11191, true)
                          | uu____11235 when Prims.op_Negation norm1 ->
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
                          | uu____11237 ->
                              let uu____11238 =
                                let uu____11239 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11240 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11239
                                  uu____11240 in
                              failwith uu____11238)
                     | uu____11253 ->
                         let uu____11254 =
                           let uu____11255 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11255.FStar_Syntax_Syntax.n in
                         (match uu____11254 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11282 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11282 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11300 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11300 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11348 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11376 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11376
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11383 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11424  ->
                            fun lb  ->
                              match uu____11424 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11475 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11475
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11478 =
                                      let uu____11486 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11486
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11478 with
                                    | (tok,decl,env2) ->
                                        let uu____11511 =
                                          let uu____11518 =
                                            let uu____11524 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11524, tok) in
                                          uu____11518 :: toks in
                                        (uu____11511, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11383 with
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
                        | uu____11626 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11631 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11631 vars)
                            else
                              (let uu____11633 =
                                 let uu____11637 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11637) in
                               FStar_SMTEncoding_Util.mkApp uu____11633) in
                      let uu____11642 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_11644  ->
                                 match uu___116_11644 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11645 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11648 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11648))) in
                      if uu____11642
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11668;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11670;
                                FStar_Syntax_Syntax.lbeff = uu____11671;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11712 =
                                 let uu____11716 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11716 with
                                 | (tcenv',uu____11727,e_t) ->
                                     let uu____11731 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11738 -> failwith "Impossible" in
                                     (match uu____11731 with
                                      | (e1,t_norm1) ->
                                          ((let uu___149_11747 = env1 in
                                            {
                                              bindings =
                                                (uu___149_11747.bindings);
                                              depth = (uu___149_11747.depth);
                                              tcenv = tcenv';
                                              warn = (uu___149_11747.warn);
                                              cache = (uu___149_11747.cache);
                                              nolabels =
                                                (uu___149_11747.nolabels);
                                              use_zfuel_name =
                                                (uu___149_11747.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___149_11747.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___149_11747.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11712 with
                                | (env',e1,t_norm1) ->
                                    let uu____11754 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11754 with
                                     | ((binders,body,uu____11766,uu____11767),curry)
                                         ->
                                         ((let uu____11774 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11774
                                           then
                                             let uu____11775 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11776 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11775 uu____11776
                                           else ());
                                          (let uu____11778 =
                                             encode_binders None binders env' in
                                           match uu____11778 with
                                           | (vars,guards,env'1,binder_decls,uu____11794)
                                               ->
                                               let body1 =
                                                 let uu____11802 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11802
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11805 =
                                                 let uu____11810 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11810
                                                 then
                                                   let uu____11816 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11817 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11816, uu____11817)
                                                 else
                                                   (let uu____11823 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11823)) in
                                               (match uu____11805 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11837 =
                                                        let uu____11841 =
                                                          let uu____11842 =
                                                            let uu____11848 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11848) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11842 in
                                                        let uu____11854 =
                                                          let uu____11856 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11856 in
                                                        (uu____11841,
                                                          uu____11854,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____11837 in
                                                    let uu____11858 =
                                                      let uu____11860 =
                                                        let uu____11862 =
                                                          let uu____11864 =
                                                            let uu____11866 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11866 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11864 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11862 in
                                                      FStar_List.append
                                                        decls1 uu____11860 in
                                                    (uu____11858, env1))))))
                           | uu____11869 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11888 = varops.fresh "fuel" in
                             (uu____11888, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____11891 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____11930  ->
                                     fun uu____11931  ->
                                       match (uu____11930, uu____11931) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12013 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12013 in
                                           let gtok =
                                             let uu____12015 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12015 in
                                           let env3 =
                                             let uu____12017 =
                                               let uu____12019 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_43  -> Some _0_43)
                                                 uu____12019 in
                                             push_free_var env2 flid gtok
                                               uu____12017 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____11891 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12105
                                 t_norm uu____12107 =
                                 match (uu____12105, uu____12107) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12134;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12135;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12152 =
                                       let uu____12156 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12156 with
                                       | (tcenv',uu____12171,e_t) ->
                                           let uu____12175 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12182 ->
                                                 failwith "Impossible" in
                                           (match uu____12175 with
                                            | (e1,t_norm1) ->
                                                ((let uu___150_12191 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___150_12191.bindings);
                                                    depth =
                                                      (uu___150_12191.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___150_12191.warn);
                                                    cache =
                                                      (uu___150_12191.cache);
                                                    nolabels =
                                                      (uu___150_12191.nolabels);
                                                    use_zfuel_name =
                                                      (uu___150_12191.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___150_12191.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___150_12191.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12152 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12201 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12201
                                            then
                                              let uu____12202 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12203 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12204 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12202 uu____12203
                                                uu____12204
                                            else ());
                                           (let uu____12206 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12206 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12228 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12228
                                                  then
                                                    let uu____12229 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12230 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12231 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12232 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12229 uu____12230
                                                      uu____12231 uu____12232
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12236 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12236 with
                                                  | (vars,guards,env'1,binder_decls,uu____12254)
                                                      ->
                                                      let decl_g =
                                                        let uu____12262 =
                                                          let uu____12268 =
                                                            let uu____12270 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12270 in
                                                          (g, uu____12268,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12262 in
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
                                                        let uu____12285 =
                                                          let uu____12289 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12289) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12285 in
                                                      let gsapp =
                                                        let uu____12295 =
                                                          let uu____12299 =
                                                            let uu____12301 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12301 ::
                                                              vars_tm in
                                                          (g, uu____12299) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12295 in
                                                      let gmax =
                                                        let uu____12305 =
                                                          let uu____12309 =
                                                            let uu____12311 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12311 ::
                                                              vars_tm in
                                                          (g, uu____12309) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12305 in
                                                      let body1 =
                                                        let uu____12315 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12315
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12317 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12317 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12328
                                                               =
                                                               let uu____12332
                                                                 =
                                                                 let uu____12333
                                                                   =
                                                                   let uu____12341
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
                                                                    uu____12341) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12333 in
                                                               let uu____12352
                                                                 =
                                                                 let uu____12354
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12354 in
                                                               (uu____12332,
                                                                 uu____12352,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12328 in
                                                           let eqn_f =
                                                             let uu____12357
                                                               =
                                                               let uu____12361
                                                                 =
                                                                 let uu____12362
                                                                   =
                                                                   let uu____12368
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12368) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12362 in
                                                               (uu____12361,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12357 in
                                                           let eqn_g' =
                                                             let uu____12376
                                                               =
                                                               let uu____12380
                                                                 =
                                                                 let uu____12381
                                                                   =
                                                                   let uu____12387
                                                                    =
                                                                    let uu____12388
                                                                    =
                                                                    let uu____12391
                                                                    =
                                                                    let uu____12392
                                                                    =
                                                                    let uu____12396
                                                                    =
                                                                    let uu____12398
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12398
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12396) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12392 in
                                                                    (gsapp,
                                                                    uu____12391) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12388 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12387) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12381 in
                                                               (uu____12380,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12376 in
                                                           let uu____12410 =
                                                             let uu____12415
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12415
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12432)
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
                                                                    let uu____12447
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12447
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12450
                                                                    =
                                                                    let uu____12454
                                                                    =
                                                                    let uu____12455
                                                                    =
                                                                    let uu____12461
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12461) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12455 in
                                                                    (uu____12454,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12450 in
                                                                 let uu____12472
                                                                   =
                                                                   let uu____12476
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12476
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12484
                                                                    =
                                                                    let uu____12486
                                                                    =
                                                                    let uu____12487
                                                                    =
                                                                    let uu____12491
                                                                    =
                                                                    let uu____12492
                                                                    =
                                                                    let uu____12498
                                                                    =
                                                                    let uu____12499
                                                                    =
                                                                    let uu____12502
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12502,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12499 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12498) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12492 in
                                                                    (uu____12491,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12487 in
                                                                    [uu____12486] in
                                                                    (d3,
                                                                    uu____12484) in
                                                                 (match uu____12472
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12410
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
                               let uu____12537 =
                                 let uu____12544 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12580  ->
                                      fun uu____12581  ->
                                        match (uu____12580, uu____12581) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12667 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12667 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12544 in
                               (match uu____12537 with
                                | (decls2,eqns,env01) ->
                                    let uu____12707 =
                                      let isDeclFun uu___117_12715 =
                                        match uu___117_12715 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12716 -> true
                                        | uu____12722 -> false in
                                      let uu____12723 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12723
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12707 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12750 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12750
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
        let uu____12783 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____12783 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____12786 = encode_sigelt' env se in
      match uu____12786 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12796 =
                  let uu____12797 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____12797 in
                [uu____12796]
            | uu____12798 ->
                let uu____12799 =
                  let uu____12801 =
                    let uu____12802 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12802 in
                  uu____12801 :: g in
                let uu____12803 =
                  let uu____12805 =
                    let uu____12806 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12806 in
                  [uu____12805] in
                FStar_List.append uu____12799 uu____12803 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____12816 =
          let uu____12817 = FStar_Syntax_Subst.compress t in
          uu____12817.FStar_Syntax_Syntax.n in
        match uu____12816 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____12821)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____12824 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12827 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____12830 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____12832 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12834 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____12842 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12845 =
            let uu____12846 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12846 Prims.op_Negation in
          if uu____12845
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12866 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_abs
                        ((ed.FStar_Syntax_Syntax.binders), tm,
                          (Some
                             (FStar_Syntax_Util.mk_residual_comp
                                FStar_Syntax_Const.effect_Tot_lid None
                                [FStar_Syntax_Syntax.TOTAL])))) None
                     tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____12886 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____12886 with
               | (aname,atok,env2) ->
                   let uu____12896 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____12896 with
                    | (formals,uu____12906) ->
                        let uu____12913 =
                          let uu____12916 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____12916 env2 in
                        (match uu____12913 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____12924 =
                                 let uu____12925 =
                                   let uu____12931 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____12939  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____12931,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____12925 in
                               [uu____12924;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____12946 =
                               let aux uu____12975 uu____12976 =
                                 match (uu____12975, uu____12976) with
                                 | ((bv,uu____13003),(env3,acc_sorts,acc)) ->
                                     let uu____13024 = gen_term_var env3 bv in
                                     (match uu____13024 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____12946 with
                              | (uu____13062,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13076 =
                                      let uu____13080 =
                                        let uu____13081 =
                                          let uu____13087 =
                                            let uu____13088 =
                                              let uu____13091 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13091) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13088 in
                                          ([[app]], xs_sorts, uu____13087) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13081 in
                                      (uu____13080, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13076 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13103 =
                                      let uu____13107 =
                                        let uu____13108 =
                                          let uu____13114 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13114) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13108 in
                                      (uu____13107,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13103 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13124 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13124 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13140,uu____13141)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13142 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13142 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13153,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13158 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13160  ->
                      match uu___118_13160 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13161 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13164 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13165 -> false)) in
            Prims.op_Negation uu____13158 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13171 = encode_top_level_val env fv t quals in
             match uu____13171 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13183 =
                   let uu____13185 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13185 in
                 (uu____13183, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13190 = encode_formula f env in
          (match uu____13190 with
           | (f1,decls) ->
               let g =
                 let uu____13199 =
                   let uu____13200 =
                     let uu____13204 =
                       let uu____13206 =
                         let uu____13207 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13207 in
                       Some uu____13206 in
                     let uu____13208 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13204, uu____13208) in
                   FStar_SMTEncoding_Util.mkAssume uu____13200 in
                 [uu____13199] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13212,attrs) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right attrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let uu____13220 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13227 =
                       let uu____13232 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13232.FStar_Syntax_Syntax.fv_name in
                     uu____13227.FStar_Syntax_Syntax.v in
                   let uu____13236 =
                     let uu____13237 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13237 in
                   if uu____13236
                   then
                     let val_decl =
                       let uu___151_13252 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___151_13252.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___151_13252.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13256 = encode_sigelt' env1 val_decl in
                     match uu____13256 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____13220 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13273,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13275;
                          FStar_Syntax_Syntax.lbtyp = uu____13276;
                          FStar_Syntax_Syntax.lbeff = uu____13277;
                          FStar_Syntax_Syntax.lbdef = uu____13278;_}::[]),uu____13279,uu____13280)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13294 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13294 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13317 =
                   let uu____13319 =
                     let uu____13320 =
                       let uu____13324 =
                         let uu____13325 =
                           let uu____13331 =
                             let uu____13332 =
                               let uu____13335 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13335) in
                             FStar_SMTEncoding_Util.mkEq uu____13332 in
                           ([[b2t_x]], [xx], uu____13331) in
                         FStar_SMTEncoding_Util.mkForall uu____13325 in
                       (uu____13324, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13320 in
                   [uu____13319] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13317 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13352,uu____13353,uu____13354)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_13360  ->
                  match uu___119_13360 with
                  | FStar_Syntax_Syntax.Discriminator uu____13361 -> true
                  | uu____13362 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13364,lids,uu____13366) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13373 =
                     let uu____13374 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13374.FStar_Ident.idText in
                   uu____13373 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_13376  ->
                     match uu___120_13376 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13377 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13380,uu____13381)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_13391  ->
                  match uu___121_13391 with
                  | FStar_Syntax_Syntax.Projector uu____13392 -> true
                  | uu____13395 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13402 = try_lookup_free_var env l in
          (match uu____13402 with
           | Some uu____13406 -> ([], env)
           | None  ->
               let se1 =
                 let uu___152_13409 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___152_13409.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___152_13409.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13415,uu____13416) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13428) ->
          let uu____13433 = encode_sigelts env ses in
          (match uu____13433 with
           | (g,env1) ->
               let uu____13443 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_13453  ->
                         match uu___122_13453 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13454;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13455;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13456;_}
                             -> false
                         | uu____13458 -> true)) in
               (match uu____13443 with
                | (g',inversions) ->
                    let uu____13467 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_13477  ->
                              match uu___123_13477 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13478 ->
                                  true
                              | uu____13484 -> false)) in
                    (match uu____13467 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13495,tps,k,uu____13498,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_13508  ->
                    match uu___124_13508 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13509 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13516 = c in
              match uu____13516 with
              | (name,args,uu____13520,uu____13521,uu____13522) ->
                  let uu____13525 =
                    let uu____13526 =
                      let uu____13532 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13539  ->
                                match uu____13539 with
                                | (uu____13543,sort,uu____13545) -> sort)) in
                      (name, uu____13532, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13526 in
                  [uu____13525]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13563 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13566 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13566 FStar_Option.isNone)) in
            if uu____13563
            then []
            else
              (let uu____13583 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13583 with
               | (xxsym,xx) ->
                   let uu____13589 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13600  ->
                             fun l  ->
                               match uu____13600 with
                               | (out,decls) ->
                                   let uu____13612 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13612 with
                                    | (uu____13618,data_t) ->
                                        let uu____13620 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13620 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13649 =
                                                 let uu____13650 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13650.FStar_Syntax_Syntax.n in
                                               match uu____13649 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13658,indices) ->
                                                   indices
                                               | uu____13674 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13686  ->
                                                         match uu____13686
                                                         with
                                                         | (x,uu____13690) ->
                                                             let uu____13691
                                                               =
                                                               let uu____13692
                                                                 =
                                                                 let uu____13696
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13696,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13692 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13691)
                                                    env) in
                                             let uu____13698 =
                                               encode_args indices env1 in
                                             (match uu____13698 with
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
                                                      let uu____13718 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13726
                                                                 =
                                                                 let uu____13729
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13729,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13726)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13718
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13731 =
                                                      let uu____13732 =
                                                        let uu____13735 =
                                                          let uu____13736 =
                                                            let uu____13739 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13739,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13736 in
                                                        (out, uu____13735) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13732 in
                                                    (uu____13731,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13589 with
                    | (data_ax,decls) ->
                        let uu____13747 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13747 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13758 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13758 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13761 =
                                 let uu____13765 =
                                   let uu____13766 =
                                     let uu____13772 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13780 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13772,
                                       uu____13780) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13766 in
                                 let uu____13788 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13765, (Some "inversion axiom"),
                                   uu____13788) in
                               FStar_SMTEncoding_Util.mkAssume uu____13761 in
                             let pattern_guarded_inversion =
                               let uu____13792 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13792
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13800 =
                                   let uu____13801 =
                                     let uu____13805 =
                                       let uu____13806 =
                                         let uu____13812 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13820 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13812, uu____13820) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13806 in
                                     let uu____13828 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13805, (Some "inversion axiom"),
                                       uu____13828) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____13801 in
                                 [uu____13800]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13831 =
            let uu____13839 =
              let uu____13840 = FStar_Syntax_Subst.compress k in
              uu____13840.FStar_Syntax_Syntax.n in
            match uu____13839 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13869 -> (tps, k) in
          (match uu____13831 with
           | (formals,res) ->
               let uu____13884 = FStar_Syntax_Subst.open_term formals res in
               (match uu____13884 with
                | (formals1,res1) ->
                    let uu____13891 = encode_binders None formals1 env in
                    (match uu____13891 with
                     | (vars,guards,env',binder_decls,uu____13906) ->
                         let uu____13913 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____13913 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____13926 =
                                  let uu____13930 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____13930) in
                                FStar_SMTEncoding_Util.mkApp uu____13926 in
                              let uu____13935 =
                                let tname_decl =
                                  let uu____13941 =
                                    let uu____13942 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____13957  ->
                                              match uu____13957 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____13965 = varops.next_id () in
                                    (tname, uu____13942,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____13965, false) in
                                  constructor_or_logic_type_decl uu____13941 in
                                let uu____13970 =
                                  match vars with
                                  | [] ->
                                      let uu____13977 =
                                        let uu____13978 =
                                          let uu____13980 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  -> Some _0_44)
                                            uu____13980 in
                                        push_free_var env1 t tname
                                          uu____13978 in
                                      ([], uu____13977)
                                  | uu____13984 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____13990 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____13990 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____13999 =
                                          let uu____14003 =
                                            let uu____14004 =
                                              let uu____14012 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14012) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14004 in
                                          (uu____14003,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____13999 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____13970 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____13935 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14035 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14035 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14049 =
                                               let uu____14050 =
                                                 let uu____14054 =
                                                   let uu____14055 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14055 in
                                                 (uu____14054,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14050 in
                                             [uu____14049]
                                           else [] in
                                         let uu____14058 =
                                           let uu____14060 =
                                             let uu____14062 =
                                               let uu____14063 =
                                                 let uu____14067 =
                                                   let uu____14068 =
                                                     let uu____14074 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14074) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14068 in
                                                 (uu____14067, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14063 in
                                             [uu____14062] in
                                           FStar_List.append karr uu____14060 in
                                         FStar_List.append decls1 uu____14058 in
                                   let aux =
                                     let uu____14083 =
                                       let uu____14085 =
                                         inversion_axioms tapp vars in
                                       let uu____14087 =
                                         let uu____14089 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14089] in
                                       FStar_List.append uu____14085
                                         uu____14087 in
                                     FStar_List.append kindingAx uu____14083 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14094,uu____14095,uu____14096,uu____14097,uu____14098)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14103,t,uu____14105,n_tps,uu____14107) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14112 = new_term_constant_and_tok_from_lid env d in
          (match uu____14112 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14123 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14123 with
                | (formals,t_res) ->
                    let uu____14145 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14145 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14154 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14154 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14192 =
                                            mk_term_projector_name d x in
                                          (uu____14192,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14194 =
                                  let uu____14204 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14204, true) in
                                FStar_All.pipe_right uu____14194
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
                              let uu____14226 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14226 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14234::uu____14235 ->
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
                                         let uu____14260 =
                                           let uu____14266 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14266) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14260
                                     | uu____14279 -> tok_typing in
                                   let uu____14284 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14284 with
                                    | (vars',guards',env'',decls_formals,uu____14299)
                                        ->
                                        let uu____14306 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14306 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14325 ->
                                                   let uu____14329 =
                                                     let uu____14330 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14330 in
                                                   [uu____14329] in
                                             let encode_elim uu____14337 =
                                               let uu____14338 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14338 with
                                               | (head1,args) ->
                                                   let uu____14367 =
                                                     let uu____14368 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14368.FStar_Syntax_Syntax.n in
                                                   (match uu____14367 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____14375;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14376;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14377;_},uu____14378)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14388 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14388
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
                                                                 | uu____14414
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14422
                                                                    =
                                                                    let uu____14423
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14423 in
                                                                    if
                                                                    uu____14422
                                                                    then
                                                                    let uu____14430
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14430]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14432
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14445
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14445
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14467
                                                                    =
                                                                    let uu____14471
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14471 in
                                                                    (match uu____14467
                                                                    with
                                                                    | 
                                                                    (uu____14478,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14484
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14484
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14486
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14486
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
                                                             (match uu____14432
                                                              with
                                                              | (uu____14494,arg_vars,elim_eqns_or_guards,uu____14497)
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
                                                                    let uu____14516
                                                                    =
                                                                    let uu____14520
                                                                    =
                                                                    let uu____14521
                                                                    =
                                                                    let uu____14527
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14533
                                                                    =
                                                                    let uu____14534
                                                                    =
                                                                    let uu____14537
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14537) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14534 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14527,
                                                                    uu____14533) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14521 in
                                                                    (uu____14520,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14516 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14550
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14550,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14552
                                                                    =
                                                                    let uu____14556
                                                                    =
                                                                    let uu____14557
                                                                    =
                                                                    let uu____14563
                                                                    =
                                                                    let uu____14566
                                                                    =
                                                                    let uu____14568
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14568] in
                                                                    [uu____14566] in
                                                                    let uu____14571
                                                                    =
                                                                    let uu____14572
                                                                    =
                                                                    let uu____14575
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14576
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14575,
                                                                    uu____14576) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14572 in
                                                                    (uu____14563,
                                                                    [x],
                                                                    uu____14571) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14557 in
                                                                    let uu____14586
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14556,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14586) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14552
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14591
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
                                                                    (let uu____14606
                                                                    =
                                                                    let uu____14607
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14607
                                                                    dapp1 in
                                                                    [uu____14606]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14591
                                                                    FStar_List.flatten in
                                                                    let uu____14611
                                                                    =
                                                                    let uu____14615
                                                                    =
                                                                    let uu____14616
                                                                    =
                                                                    let uu____14622
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14628
                                                                    =
                                                                    let uu____14629
                                                                    =
                                                                    let uu____14632
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14632) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14629 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14622,
                                                                    uu____14628) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14616 in
                                                                    (uu____14615,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14611) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14648 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14648
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
                                                                 | uu____14674
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14682
                                                                    =
                                                                    let uu____14683
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14683 in
                                                                    if
                                                                    uu____14682
                                                                    then
                                                                    let uu____14690
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14690]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14692
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14705
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14705
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14727
                                                                    =
                                                                    let uu____14731
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14731 in
                                                                    (match uu____14727
                                                                    with
                                                                    | 
                                                                    (uu____14738,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14744
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14744
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14746
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14746
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
                                                             (match uu____14692
                                                              with
                                                              | (uu____14754,arg_vars,elim_eqns_or_guards,uu____14757)
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
                                                                    let uu____14776
                                                                    =
                                                                    let uu____14780
                                                                    =
                                                                    let uu____14781
                                                                    =
                                                                    let uu____14787
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14793
                                                                    =
                                                                    let uu____14794
                                                                    =
                                                                    let uu____14797
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14797) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14794 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14787,
                                                                    uu____14793) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14781 in
                                                                    (uu____14780,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14776 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14810
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14810,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14812
                                                                    =
                                                                    let uu____14816
                                                                    =
                                                                    let uu____14817
                                                                    =
                                                                    let uu____14823
                                                                    =
                                                                    let uu____14826
                                                                    =
                                                                    let uu____14828
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14828] in
                                                                    [uu____14826] in
                                                                    let uu____14831
                                                                    =
                                                                    let uu____14832
                                                                    =
                                                                    let uu____14835
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14836
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14835,
                                                                    uu____14836) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14832 in
                                                                    (uu____14823,
                                                                    [x],
                                                                    uu____14831) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14817 in
                                                                    let uu____14846
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14816,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14846) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14812
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14851
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
                                                                    (let uu____14866
                                                                    =
                                                                    let uu____14867
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14867
                                                                    dapp1 in
                                                                    [uu____14866]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14851
                                                                    FStar_List.flatten in
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
                                                                    prec in
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
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14871) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14902 ->
                                                        ((let uu____14904 =
                                                            let uu____14905 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14906 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14905
                                                              uu____14906 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14904);
                                                         ([], []))) in
                                             let uu____14909 = encode_elim () in
                                             (match uu____14909 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14921 =
                                                      let uu____14923 =
                                                        let uu____14925 =
                                                          let uu____14927 =
                                                            let uu____14929 =
                                                              let uu____14930
                                                                =
                                                                let uu____14936
                                                                  =
                                                                  let uu____14938
                                                                    =
                                                                    let uu____14939
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14939 in
                                                                  Some
                                                                    uu____14938 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14936) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14930 in
                                                            [uu____14929] in
                                                          let uu____14942 =
                                                            let uu____14944 =
                                                              let uu____14946
                                                                =
                                                                let uu____14948
                                                                  =
                                                                  let uu____14950
                                                                    =
                                                                    let uu____14952
                                                                    =
                                                                    let uu____14954
                                                                    =
                                                                    let uu____14955
                                                                    =
                                                                    let uu____14959
                                                                    =
                                                                    let uu____14960
                                                                    =
                                                                    let uu____14966
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14966) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14960 in
                                                                    (uu____14959,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14955 in
                                                                    let uu____14973
                                                                    =
                                                                    let uu____14975
                                                                    =
                                                                    let uu____14976
                                                                    =
                                                                    let uu____14980
                                                                    =
                                                                    let uu____14981
                                                                    =
                                                                    let uu____14987
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14993
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14987,
                                                                    uu____14993) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14981 in
                                                                    (uu____14980,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14976 in
                                                                    [uu____14975] in
                                                                    uu____14954
                                                                    ::
                                                                    uu____14973 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14952 in
                                                                  FStar_List.append
                                                                    uu____14950
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14948 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14946 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14944 in
                                                          FStar_List.append
                                                            uu____14927
                                                            uu____14942 in
                                                        FStar_List.append
                                                          decls3 uu____14925 in
                                                      FStar_List.append
                                                        decls2 uu____14923 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14921 in
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
           (fun uu____15014  ->
              fun se  ->
                match uu____15014 with
                | (g,env1) ->
                    let uu____15026 = encode_sigelt env1 se in
                    (match uu____15026 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15062 =
        match uu____15062 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15080 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____15085 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15085
                   then
                     let uu____15086 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15087 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15088 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15086 uu____15087 uu____15088
                   else ());
                  (let uu____15090 = encode_term t1 env1 in
                   match uu____15090 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15100 =
                         let uu____15104 =
                           let uu____15105 =
                             let uu____15106 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15106
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15105 in
                         new_term_constant_from_string env1 x uu____15104 in
                       (match uu____15100 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15117 = FStar_Options.log_queries () in
                              if uu____15117
                              then
                                let uu____15119 =
                                  let uu____15120 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15121 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15122 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15120 uu____15121 uu____15122 in
                                Some uu____15119
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15133,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15142 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15142 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15155,se,uu____15157) ->
                 let uu____15160 = encode_sigelt env1 se in
                 (match uu____15160 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15170,se) ->
                 let uu____15174 = encode_sigelt env1 se in
                 (match uu____15174 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15184 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15184 with | (uu____15196,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15241  ->
            match uu____15241 with
            | (l,uu____15248,uu____15249) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15270  ->
            match uu____15270 with
            | (l,uu____15278,uu____15279) ->
                let uu____15284 =
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45) (
                    fst l) in
                let uu____15285 =
                  let uu____15287 =
                    let uu____15288 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15288 in
                  [uu____15287] in
                uu____15284 :: uu____15285)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15299 =
      let uu____15301 =
        let uu____15302 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15304 =
          let uu____15305 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15305 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15302;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15304
        } in
      [uu____15301] in
    FStar_ST.write last_env uu____15299
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15315 = FStar_ST.read last_env in
      match uu____15315 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15321 ->
          let uu___153_15323 = e in
          let uu____15324 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___153_15323.bindings);
            depth = (uu___153_15323.depth);
            tcenv;
            warn = (uu___153_15323.warn);
            cache = (uu___153_15323.cache);
            nolabels = (uu___153_15323.nolabels);
            use_zfuel_name = (uu___153_15323.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___153_15323.encode_non_total_function_typ);
            current_module_name = uu____15324
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15328 = FStar_ST.read last_env in
    match uu____15328 with
    | [] -> failwith "Empty env stack"
    | uu____15333::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15341  ->
    let uu____15342 = FStar_ST.read last_env in
    match uu____15342 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___154_15353 = hd1 in
          {
            bindings = (uu___154_15353.bindings);
            depth = (uu___154_15353.depth);
            tcenv = (uu___154_15353.tcenv);
            warn = (uu___154_15353.warn);
            cache = refs;
            nolabels = (uu___154_15353.nolabels);
            use_zfuel_name = (uu___154_15353.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15353.encode_non_total_function_typ);
            current_module_name = (uu___154_15353.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15359  ->
    let uu____15360 = FStar_ST.read last_env in
    match uu____15360 with
    | [] -> failwith "Popping an empty stack"
    | uu____15365::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15373  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15376  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15379  ->
    let uu____15380 = FStar_ST.read last_env in
    match uu____15380 with
    | hd1::uu____15386::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15392 -> failwith "Impossible"
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
        | (uu____15441::uu____15442,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___155_15446 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___155_15446.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___155_15446.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___155_15446.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15447 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15458 =
        let uu____15460 =
          let uu____15461 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15461 in
        let uu____15462 = open_fact_db_tags env in uu____15460 :: uu____15462 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15458
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
      let uu____15477 = encode_sigelt env se in
      match uu____15477 with
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
        let uu____15502 = FStar_Options.log_queries () in
        if uu____15502
        then
          let uu____15504 =
            let uu____15505 =
              let uu____15506 =
                let uu____15507 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15507 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15506 in
            FStar_SMTEncoding_Term.Caption uu____15505 in
          uu____15504 :: decls
        else decls in
      let env =
        let uu____15514 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15514 tcenv in
      let uu____15515 = encode_top_level_facts env se in
      match uu____15515 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15524 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15524))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15535 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15535
       then
         let uu____15536 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15536
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15557  ->
                 fun se  ->
                   match uu____15557 with
                   | (g,env2) ->
                       let uu____15569 = encode_top_level_facts env2 se in
                       (match uu____15569 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15582 =
         encode_signature
           (let uu___156_15586 = env in
            {
              bindings = (uu___156_15586.bindings);
              depth = (uu___156_15586.depth);
              tcenv = (uu___156_15586.tcenv);
              warn = false;
              cache = (uu___156_15586.cache);
              nolabels = (uu___156_15586.nolabels);
              use_zfuel_name = (uu___156_15586.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_15586.encode_non_total_function_typ);
              current_module_name = (uu___156_15586.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15582 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15598 = FStar_Options.log_queries () in
             if uu____15598
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___157_15603 = env1 in
               {
                 bindings = (uu___157_15603.bindings);
                 depth = (uu___157_15603.depth);
                 tcenv = (uu___157_15603.tcenv);
                 warn = true;
                 cache = (uu___157_15603.cache);
                 nolabels = (uu___157_15603.nolabels);
                 use_zfuel_name = (uu___157_15603.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___157_15603.encode_non_total_function_typ);
                 current_module_name = (uu___157_15603.current_module_name)
               });
            (let uu____15605 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15605
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
        (let uu____15640 =
           let uu____15641 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15641.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15640);
        (let env =
           let uu____15643 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15643 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15650 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15671 = aux rest in
                 (match uu____15671 with
                  | (out,rest1) ->
                      let t =
                        let uu____15689 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15689 with
                        | Some uu____15693 ->
                            let uu____15694 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15694
                              x.FStar_Syntax_Syntax.sort
                        | uu____15695 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15698 =
                        let uu____15700 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___158_15701 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_15701.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_15701.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15700 :: out in
                      (uu____15698, rest1))
             | uu____15704 -> ([], bindings1) in
           let uu____15708 = aux bindings in
           match uu____15708 with
           | (closing,bindings1) ->
               let uu____15722 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15722, bindings1) in
         match uu____15650 with
         | (q1,bindings1) ->
             let uu____15735 =
               let uu____15738 =
                 FStar_List.filter
                   (fun uu___125_15740  ->
                      match uu___125_15740 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15741 ->
                          false
                      | uu____15745 -> true) bindings1 in
               encode_env_bindings env uu____15738 in
             (match uu____15735 with
              | (env_decls,env1) ->
                  ((let uu____15756 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15756
                    then
                      let uu____15757 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15757
                    else ());
                   (let uu____15759 = encode_formula q1 env1 in
                    match uu____15759 with
                    | (phi,qdecls) ->
                        let uu____15771 =
                          let uu____15774 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15774 phi in
                        (match uu____15771 with
                         | (labels,phi1) ->
                             let uu____15784 = encode_labels labels in
                             (match uu____15784 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15805 =
                                      let uu____15809 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15810 =
                                        varops.mk_unique "@query" in
                                      (uu____15809, (Some "query"),
                                        uu____15810) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____15805 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15823 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15823 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15825 = encode_formula q env in
       match uu____15825 with
       | (f,uu____15829) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15831) -> true
             | uu____15834 -> false)))