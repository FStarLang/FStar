open Prims
let add_fuel x tl1 =
  let uu____19 = FStar_Options.unthrottle_inductives () in
  if uu____19 then tl1 else x :: tl1
let withenv c uu____47 = match uu____47 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___101_86  ->
       match uu___101_86 with
       | (FStar_Util.Inl uu____91,uu____92) -> false
       | uu____95 -> true) args
let subst_lcomp_opt s l =
  match l with
  | Some (FStar_Util.Inl l1) ->
      let uu____129 =
        let uu____132 =
          let uu____133 =
            let uu____136 = l1.FStar_Syntax_Syntax.comp () in
            FStar_Syntax_Subst.subst_comp s uu____136 in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____133 in
        FStar_Util.Inl uu____132 in
      Some uu____129
  | uu____141 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_'
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___125_158 = a in
        let uu____159 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____159;
          FStar_Syntax_Syntax.index =
            (uu___125_158.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___125_158.FStar_Syntax_Syntax.sort)
        } in
      let uu____160 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____160
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____176 =
          let uu____177 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____177 in
        let uu____178 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____178 with
        | (uu____181,t) ->
            let uu____183 =
              let uu____184 = FStar_Syntax_Subst.compress t in
              uu____184.FStar_Syntax_Syntax.n in
            (match uu____183 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____199 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____199 with
                  | (binders,uu____203) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid (fst b)))
             | uu____216 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____225 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____225
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____234 =
        let uu____237 = mk_term_projector_name lid a in
        (uu____237,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____234
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____246 =
        let uu____249 = mk_term_projector_name_by_pos lid i in
        (uu____249,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____246
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
  let new_scope uu____489 =
    let uu____490 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____492 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____490, uu____492) in
  let scopes =
    let uu____503 = let uu____509 = new_scope () in [uu____509] in
    FStar_Util.mk_ref uu____503 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____534 =
        let uu____536 = FStar_ST.read scopes in
        FStar_Util.find_map uu____536
          (fun uu____553  ->
             match uu____553 with
             | (names1,uu____560) -> FStar_Util.smap_try_find names1 y1) in
      match uu____534 with
      | None  -> y1
      | Some uu____565 ->
          (FStar_Util.incr ctr;
           (let uu____570 =
              let uu____571 =
                let uu____572 = FStar_ST.read ctr in
                Prims.string_of_int uu____572 in
              Prims.strcat "__" uu____571 in
            Prims.strcat y1 uu____570)) in
    let top_scope =
      let uu____577 =
        let uu____582 = FStar_ST.read scopes in FStar_List.hd uu____582 in
      FStar_All.pipe_left FStar_Pervasives.fst uu____577 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____621 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____632 =
      let uu____633 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____633 in
    FStar_Util.format2 "%s_%s" pfx uu____632 in
  let string_const s =
    let uu____638 =
      let uu____640 = FStar_ST.read scopes in
      FStar_Util.find_map uu____640
        (fun uu____657  ->
           match uu____657 with
           | (uu____663,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____638 with
    | Some f -> f
    | None  ->
        let id = next_id1 () in
        let f =
          let uu____672 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____672 in
        let top_scope =
          let uu____675 =
            let uu____680 = FStar_ST.read scopes in FStar_List.hd uu____680 in
          FStar_All.pipe_left FStar_Pervasives.snd uu____675 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____708 =
    let uu____709 =
      let uu____715 = new_scope () in
      let uu____720 = FStar_ST.read scopes in uu____715 :: uu____720 in
    FStar_ST.write scopes uu____709 in
  let pop1 uu____747 =
    let uu____748 =
      let uu____754 = FStar_ST.read scopes in FStar_List.tl uu____754 in
    FStar_ST.write scopes uu____748 in
  let mark1 uu____781 = push1 () in
  let reset_mark1 uu____785 = pop1 () in
  let commit_mark1 uu____789 =
    let uu____790 = FStar_ST.read scopes in
    match uu____790 with
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
    | uu____850 -> failwith "Impossible" in
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
    let uu___126_860 = x in
    let uu____861 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____861;
      FStar_Syntax_Syntax.index = (uu___126_860.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___126_860.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term option* FStar_SMTEncoding_Term.term option)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____885 -> false
let __proj__Binding_var__item___0:
  binding -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____911 -> false
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
         (fun uu___102_1121  ->
            match uu___102_1121 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1124 -> [])) in
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
    let uu____1134 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___103_1138  ->
              match uu___103_1138 with
              | Binding_var (x,uu____1140) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1142,uu____1143,uu____1144) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1134 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string option =
  fun env  ->
    fun t  ->
      let uu____1182 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1182
      then
        let uu____1184 = FStar_Syntax_Print.term_to_string t in
        Some uu____1184
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1197 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1197)
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
        (let uu___127_1211 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___127_1211.tcenv);
           warn = (uu___127_1211.warn);
           cache = (uu___127_1211.cache);
           nolabels = (uu___127_1211.nolabels);
           use_zfuel_name = (uu___127_1211.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___127_1211.encode_non_total_function_typ);
           current_module_name = (uu___127_1211.current_module_name)
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
        (let uu___128_1226 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___128_1226.depth);
           tcenv = (uu___128_1226.tcenv);
           warn = (uu___128_1226.warn);
           cache = (uu___128_1226.cache);
           nolabels = (uu___128_1226.nolabels);
           use_zfuel_name = (uu___128_1226.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_1226.encode_non_total_function_typ);
           current_module_name = (uu___128_1226.current_module_name)
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
          (let uu___129_1245 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___129_1245.depth);
             tcenv = (uu___129_1245.tcenv);
             warn = (uu___129_1245.warn);
             cache = (uu___129_1245.cache);
             nolabels = (uu___129_1245.nolabels);
             use_zfuel_name = (uu___129_1245.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___129_1245.encode_non_total_function_typ);
             current_module_name = (uu___129_1245.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___130_1258 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___130_1258.depth);
          tcenv = (uu___130_1258.tcenv);
          warn = (uu___130_1258.warn);
          cache = (uu___130_1258.cache);
          nolabels = (uu___130_1258.nolabels);
          use_zfuel_name = (uu___130_1258.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___130_1258.encode_non_total_function_typ);
          current_module_name = (uu___130_1258.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___104_1276  ->
             match uu___104_1276 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1284 -> None) in
      let uu____1287 = aux a in
      match uu____1287 with
      | None  ->
          let a2 = unmangle a in
          let uu____1294 = aux a2 in
          (match uu____1294 with
           | None  ->
               let uu____1300 =
                 let uu____1301 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1302 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1301 uu____1302 in
               failwith uu____1300
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1324 =
        let uu___131_1325 = env in
        let uu____1326 =
          let uu____1328 =
            let uu____1329 =
              let uu____1336 =
                let uu____1338 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_39  -> Some _0_39) uu____1338 in
              (x, fname, uu____1336, None) in
            Binding_fvar uu____1329 in
          uu____1328 :: (env.bindings) in
        {
          bindings = uu____1326;
          depth = (uu___131_1325.depth);
          tcenv = (uu___131_1325.tcenv);
          warn = (uu___131_1325.warn);
          cache = (uu___131_1325.cache);
          nolabels = (uu___131_1325.nolabels);
          use_zfuel_name = (uu___131_1325.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_1325.encode_non_total_function_typ);
          current_module_name = (uu___131_1325.current_module_name)
        } in
      (fname, ftok, uu____1324)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option) option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___105_1362  ->
           match uu___105_1362 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1384 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1398 =
        lookup_binding env
          (fun uu___106_1400  ->
             match uu___106_1400 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1410 -> None) in
      FStar_All.pipe_right uu____1398 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option)
  =
  fun env  ->
    fun a  ->
      let uu____1425 = try_lookup_lid env a in
      match uu____1425 with
      | None  ->
          let uu____1442 =
            let uu____1443 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1443 in
          failwith uu____1442
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
          let uu___132_1478 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___132_1478.depth);
            tcenv = (uu___132_1478.tcenv);
            warn = (uu___132_1478.warn);
            cache = (uu___132_1478.cache);
            nolabels = (uu___132_1478.nolabels);
            use_zfuel_name = (uu___132_1478.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___132_1478.encode_non_total_function_typ);
            current_module_name = (uu___132_1478.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1493 = lookup_lid env x in
        match uu____1493 with
        | (t1,t2,uu____1501) ->
            let t3 =
              let uu____1507 =
                let uu____1511 =
                  let uu____1513 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1513] in
                (f, uu____1511) in
              FStar_SMTEncoding_Util.mkApp uu____1507 in
            let uu___133_1516 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___133_1516.depth);
              tcenv = (uu___133_1516.tcenv);
              warn = (uu___133_1516.warn);
              cache = (uu___133_1516.cache);
              nolabels = (uu___133_1516.nolabels);
              use_zfuel_name = (uu___133_1516.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___133_1516.encode_non_total_function_typ);
              current_module_name = (uu___133_1516.current_module_name)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term option =
  fun env  ->
    fun l  ->
      let uu____1528 = try_lookup_lid env l in
      match uu____1528 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1555 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1560,fuel::[]) ->
                         let uu____1563 =
                           let uu____1564 =
                             let uu____1565 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1565
                               FStar_Pervasives.fst in
                           FStar_Util.starts_with uu____1564 "fuel" in
                         if uu____1563
                         then
                           let uu____1567 =
                             let uu____1568 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1568
                               fuel in
                           FStar_All.pipe_left (fun _0_40  -> Some _0_40)
                             uu____1567
                         else Some t
                     | uu____1571 -> Some t)
                | uu____1572 -> None))
let lookup_free_var env a =
  let uu____1593 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1593 with
  | Some t -> t
  | None  ->
      let uu____1596 =
        let uu____1597 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1597 in
      failwith uu____1596
let lookup_free_var_name env a =
  let uu____1617 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1617 with | (x,uu____1624,uu____1625) -> x
let lookup_free_var_sym env a =
  let uu____1652 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1652 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1673;
             FStar_SMTEncoding_Term.rng = uu____1674;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1682 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1696 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name: env_t -> Prims.string -> FStar_SMTEncoding_Term.term option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___107_1707  ->
           match uu___107_1707 with
           | Binding_fvar (uu____1709,nm',tok,uu____1712) when nm = nm' ->
               tok
           | uu____1717 -> None)
let mkForall_fuel' n1 uu____1737 =
  match uu____1737 with
  | (pats,vars,body) ->
      let fallback uu____1753 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1756 = FStar_Options.unthrottle_inductives () in
      if uu____1756
      then fallback ()
      else
        (let uu____1758 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1758 with
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
                       | uu____1777 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1791 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1791
                     | uu____1793 ->
                         let uu____1794 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1794 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1797 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____1826 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____1834 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____1839 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____1840 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____1849 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____1864 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1866 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1866 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____1880;
             FStar_Syntax_Syntax.pos = uu____1881;
             FStar_Syntax_Syntax.vars = uu____1882;_},uu____1883)
          ->
          let uu____1898 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1898 FStar_Option.isNone
      | uu____1911 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1920 =
        let uu____1921 = FStar_Syntax_Util.un_uinst t in
        uu____1921.FStar_Syntax_Syntax.n in
      match uu____1920 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1924,uu____1925,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___108_1954  ->
                  match uu___108_1954 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1955 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1956,uu____1957,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1984 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1984 FStar_Option.isSome
      | uu____1997 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____2006 = head_normal env t in
      if uu____2006
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
    let uu____2020 =
      let uu____2021 = FStar_Syntax_Syntax.null_binder t in [uu____2021] in
    let uu____2022 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____2020 uu____2022 None
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
                    let uu____2051 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____2051
                | s ->
                    let uu____2054 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____2054) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___109_2069  ->
    match uu___109_2069 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____2070 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____2101;
                       FStar_SMTEncoding_Term.rng = uu____2102;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____2116) ->
              let uu____2121 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____2135 -> false) args (FStar_List.rev xs)) in
              if uu____2121 then tok_of_name env f else None
          | (uu____2138,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____2141 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____2143 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____2143)) in
              if uu____2141 then Some t else None
          | uu____2146 -> None in
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
    | uu____2245 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___110_2249  ->
    match uu___110_2249 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2251 =
          let uu____2255 =
            let uu____2257 =
              let uu____2258 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2258 in
            [uu____2257] in
          ("FStar.Char.Char", uu____2255) in
        FStar_SMTEncoding_Util.mkApp uu____2251
    | FStar_Const.Const_int (i,None ) ->
        let uu____2266 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2266
    | FStar_Const.Const_int (i,Some uu____2268) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2277) ->
        let uu____2280 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2280
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2284 =
          let uu____2285 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2285 in
        failwith uu____2284
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2306 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2314 ->
            let uu____2319 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2319
        | uu____2320 ->
            if norm1
            then let uu____2321 = whnf env t1 in aux false uu____2321
            else
              (let uu____2323 =
                 let uu____2324 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2325 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2324 uu____2325 in
               failwith uu____2323) in
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
    | uu____2347 ->
        let uu____2348 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2348)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2380::uu____2381::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Syntax_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2384::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2386 -> false
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
        (let uu____2524 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2524
         then
           let uu____2525 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2525
         else ());
        (let uu____2527 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2563  ->
                   fun b  ->
                     match uu____2563 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2606 =
                           let x = unmangle (fst b) in
                           let uu____2615 = gen_term_var env1 x in
                           match uu____2615 with
                           | (xxsym,xx,env') ->
                               let uu____2629 =
                                 let uu____2632 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2632 env1 xx in
                               (match uu____2629 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2606 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2527 with
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
          let uu____2720 = encode_term t env in
          match uu____2720 with
          | (t1,decls) ->
              let uu____2727 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2727, decls)
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
          let uu____2735 = encode_term t env in
          match uu____2735 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2744 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2744, decls)
               | Some f ->
                   let uu____2746 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2746, decls))
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
        let uu____2752 = encode_args args_e env in
        match uu____2752 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2764 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____2771 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____2771 in
            let binary arg_tms1 =
              let uu____2780 =
                let uu____2781 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____2781 in
              let uu____2782 =
                let uu____2783 =
                  let uu____2784 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2784 in
                FStar_SMTEncoding_Term.unboxInt uu____2783 in
              (uu____2780, uu____2782) in
            let mk_default uu____2789 =
              let uu____2790 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2790 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____2835 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2835
              then
                let uu____2836 = let uu____2837 = mk_args ts in op uu____2837 in
                FStar_All.pipe_right uu____2836 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____2860 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____2860
              then
                let uu____2861 = binary ts in
                match uu____2861 with
                | (t1,t2) ->
                    let uu____2866 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____2866
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2869 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____2869
                 then
                   let uu____2870 = op (binary ts) in
                   FStar_All.pipe_right uu____2870
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
            let uu____2960 =
              let uu____2966 =
                FStar_List.tryFind
                  (fun uu____2978  ->
                     match uu____2978 with
                     | (l,uu____2985) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____2966 FStar_Util.must in
            (match uu____2960 with
             | (uu____3010,op) ->
                 let uu____3018 = op arg_tms in (uu____3018, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____3025 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____3025
       then
         let uu____3026 = FStar_Syntax_Print.tag_of_term t in
         let uu____3027 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____3028 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3026 uu____3027
           uu____3028
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3032 ->
           let uu____3053 =
             let uu____3054 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____3055 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____3056 = FStar_Syntax_Print.term_to_string t0 in
             let uu____3057 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3054
               uu____3055 uu____3056 uu____3057 in
           failwith uu____3053
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3060 =
             let uu____3061 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____3062 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____3063 = FStar_Syntax_Print.term_to_string t0 in
             let uu____3064 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3061
               uu____3062 uu____3063 uu____3064 in
           failwith uu____3060
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____3068 =
             let uu____3069 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____3069 in
           failwith uu____3068
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____3074) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3104) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____3113 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____3113, [])
       | FStar_Syntax_Syntax.Tm_type uu____3119 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3122) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3128 = encode_const c in (uu____3128, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____3143 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____3143 with
            | (binders1,res) ->
                let uu____3150 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____3150
                then
                  let uu____3153 = encode_binders None binders1 env in
                  (match uu____3153 with
                   | (vars,guards,env',decls,uu____3168) ->
                       let fsym =
                         let uu____3178 = varops.fresh "f" in
                         (uu____3178, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____3181 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___134_3185 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___134_3185.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___134_3185.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___134_3185.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___134_3185.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___134_3185.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___134_3185.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___134_3185.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___134_3185.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___134_3185.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___134_3185.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___134_3185.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___134_3185.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___134_3185.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___134_3185.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___134_3185.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___134_3185.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___134_3185.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___134_3185.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___134_3185.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___134_3185.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___134_3185.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___134_3185.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___134_3185.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___134_3185.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___134_3185.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___134_3185.FStar_TypeChecker_Env.is_native_tactic)
                            }) res in
                       (match uu____3181 with
                        | (pre_opt,res_t) ->
                            let uu____3192 =
                              encode_term_pred None res_t env' app in
                            (match uu____3192 with
                             | (res_pred,decls') ->
                                 let uu____3199 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____3206 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____3206, [])
                                   | Some pre ->
                                       let uu____3209 =
                                         encode_formula pre env' in
                                       (match uu____3209 with
                                        | (guard,decls0) ->
                                            let uu____3217 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3217, decls0)) in
                                 (match uu____3199 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3225 =
                                          let uu____3231 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3231) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3225 in
                                      let cvars =
                                        let uu____3241 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3241
                                          (FStar_List.filter
                                             (fun uu____3247  ->
                                                match uu____3247 with
                                                | (x,uu____3251) ->
                                                    x <> (fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3262 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3262 with
                                       | Some cache_entry ->
                                           let uu____3267 =
                                             let uu____3268 =
                                               let uu____3272 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3272) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3268 in
                                           (uu____3267,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____3283 =
                                               let uu____3284 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3284 in
                                             varops.mk_unique uu____3283 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars in
                                           let caption =
                                             let uu____3291 =
                                               FStar_Options.log_queries () in
                                             if uu____3291
                                             then
                                               let uu____3293 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____3293
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3299 =
                                               let uu____3303 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3303) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3299 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3311 =
                                               let uu____3315 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3315, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3311 in
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
                                             let uu____3328 =
                                               let uu____3332 =
                                                 let uu____3333 =
                                                   let uu____3339 =
                                                     let uu____3340 =
                                                       let uu____3343 =
                                                         let uu____3344 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3344 in
                                                       (f_has_t, uu____3343) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3340 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3339) in
                                                 mkForall_fuel uu____3333 in
                                               (uu____3332,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3328 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3357 =
                                               let uu____3361 =
                                                 let uu____3362 =
                                                   let uu____3368 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3368) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3362 in
                                               (uu____3361, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3357 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3382 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3382);
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
                     let uu____3393 =
                       let uu____3397 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3397, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3393 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3406 =
                       let uu____3410 =
                         let uu____3411 =
                           let uu____3417 =
                             let uu____3418 =
                               let uu____3421 =
                                 let uu____3422 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3422 in
                               (f_has_t, uu____3421) in
                             FStar_SMTEncoding_Util.mkImp uu____3418 in
                           ([[f_has_t]], [fsym], uu____3417) in
                         mkForall_fuel uu____3411 in
                       (uu____3410, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3406 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3436 ->
           let uu____3441 =
             let uu____3444 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3444 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3449;
                 FStar_Syntax_Syntax.pos = uu____3450;
                 FStar_Syntax_Syntax.vars = uu____3451;_} ->
                 let uu____3458 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____3458 with
                  | (b,f1) ->
                      let uu____3472 =
                        let uu____3473 = FStar_List.hd b in fst uu____3473 in
                      (uu____3472, f1))
             | uu____3478 -> failwith "impossible" in
           (match uu____3441 with
            | (x,f) ->
                let uu____3485 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3485 with
                 | (base_t,decls) ->
                     let uu____3492 = gen_term_var env x in
                     (match uu____3492 with
                      | (x1,xtm,env') ->
                          let uu____3501 = encode_formula f env' in
                          (match uu____3501 with
                           | (refinement,decls') ->
                               let uu____3508 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3508 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3519 =
                                        let uu____3521 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3525 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3521
                                          uu____3525 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3519 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3541  ->
                                              match uu____3541 with
                                              | (y,uu____3545) ->
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
                                    let uu____3564 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3564 with
                                     | Some cache_entry ->
                                         let uu____3569 =
                                           let uu____3570 =
                                             let uu____3574 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3574) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3570 in
                                         (uu____3569,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3586 =
                                             let uu____3587 =
                                               let uu____3588 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3588 in
                                             Prims.strcat module_name
                                               uu____3587 in
                                           varops.mk_unique uu____3586 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3597 =
                                             let uu____3601 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3601) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3597 in
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
                                           let uu____3612 =
                                             let uu____3616 =
                                               let uu____3617 =
                                                 let uu____3623 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3623) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3617 in
                                             (uu____3616,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3612 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____3638 =
                                             let uu____3642 =
                                               let uu____3643 =
                                                 let uu____3649 =
                                                   let uu____3650 =
                                                     let uu____3653 =
                                                       let uu____3654 =
                                                         let uu____3660 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____3660) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____3654 in
                                                     (uu____3653, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____3650 in
                                                 ([[valid_t]], cvars1,
                                                   uu____3649) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3643 in
                                             (uu____3642,
                                               (Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3638 in
                                         let t_kinding =
                                           let uu____3680 =
                                             let uu____3684 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3684,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3680 in
                                         let t_interp =
                                           let uu____3694 =
                                             let uu____3698 =
                                               let uu____3699 =
                                                 let uu____3705 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3705) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3699 in
                                             let uu____3717 =
                                               let uu____3719 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3719 in
                                             (uu____3698, uu____3717,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3694 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3724 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3724);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3741 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3741 in
           let uu____3742 = encode_term_pred None k env ttm in
           (match uu____3742 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3750 =
                    let uu____3754 =
                      let uu____3755 =
                        let uu____3756 =
                          let uu____3757 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3757 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3756 in
                      varops.mk_unique uu____3755 in
                    (t_has_k, (Some "Uvar typing"), uu____3754) in
                  FStar_SMTEncoding_Util.mkAssume uu____3750 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3760 ->
           let uu____3770 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3770 with
            | (head1,args_e) ->
                let uu____3798 =
                  let uu____3806 =
                    let uu____3807 = FStar_Syntax_Subst.compress head1 in
                    uu____3807.FStar_Syntax_Syntax.n in
                  (uu____3806, args_e) in
                (match uu____3798 with
                 | uu____3817 when head_redex env head1 ->
                     let uu____3825 = whnf env t in
                     encode_term uu____3825 env
                 | uu____3826 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____3839;
                       FStar_Syntax_Syntax.pos = uu____3840;
                       FStar_Syntax_Syntax.vars = uu____3841;_},uu____3842),uu____3843::
                    (v1,uu____3845)::(v2,uu____3847)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3885 = encode_term v1 env in
                     (match uu____3885 with
                      | (v11,decls1) ->
                          let uu____3892 = encode_term v2 env in
                          (match uu____3892 with
                           | (v21,decls2) ->
                               let uu____3899 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3899,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3902::(v1,uu____3904)::(v2,uu____3906)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3940 = encode_term v1 env in
                     (match uu____3940 with
                      | (v11,decls1) ->
                          let uu____3947 = encode_term v2 env in
                          (match uu____3947 with
                           | (v21,decls2) ->
                               let uu____3954 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3954,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3956) ->
                     let e0 =
                       let uu____3968 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3968 in
                     ((let uu____3974 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3974
                       then
                         let uu____3975 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3975
                       else ());
                      (let e =
                         let uu____3980 =
                           let uu____3981 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3982 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3981
                             uu____3982 in
                         uu____3980 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3991),(arg,uu____3993)::[]) -> encode_term arg env
                 | uu____4011 ->
                     let uu____4019 = encode_args args_e env in
                     (match uu____4019 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____4052 = encode_term head1 env in
                            match uu____4052 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____4091 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____4091 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____4135  ->
                                                 fun uu____4136  ->
                                                   match (uu____4135,
                                                           uu____4136)
                                                   with
                                                   | ((bv,uu____4150),
                                                      (a,uu____4152)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____4166 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____4166
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____4171 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____4171 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____4181 =
                                                   let uu____4185 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____4190 =
                                                     let uu____4191 =
                                                       let uu____4192 =
                                                         let uu____4193 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____4193 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____4192 in
                                                     varops.mk_unique
                                                       uu____4191 in
                                                   (uu____4185,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____4190) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____4181 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____4210 = lookup_free_var_sym env fv in
                            match uu____4210 with
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
                                   FStar_Syntax_Syntax.tk = uu____4233;
                                   FStar_Syntax_Syntax.pos = uu____4234;
                                   FStar_Syntax_Syntax.vars = uu____4235;_},uu____4236)
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____4247;
                                   FStar_Syntax_Syntax.pos = uu____4248;
                                   FStar_Syntax_Syntax.vars = uu____4249;_},uu____4250)
                                ->
                                let uu____4255 =
                                  let uu____4256 =
                                    let uu____4259 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4259
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4256
                                    FStar_Pervasives.snd in
                                Some uu____4255
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4279 =
                                  let uu____4280 =
                                    let uu____4283 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4283
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4280
                                    FStar_Pervasives.snd in
                                Some uu____4279
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4302,(FStar_Util.Inl t1,uu____4304),uu____4305)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4343,(FStar_Util.Inr c,uu____4345),uu____4346)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4384 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4404 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4404 in
                               let uu____4405 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4405 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4415;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4416;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4417;_},uu____4418)
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
                                     | uu____4450 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4500 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4500 with
            | (bs1,body1,opening) ->
                let fallback uu____4515 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____4520 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4520, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4531 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____4531
                  | FStar_Util.Inr (eff,uu____4533) ->
                      let uu____4539 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____4539 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4584 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___135_4585 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___135_4585.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___135_4585.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___135_4585.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___135_4585.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___135_4585.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___135_4585.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___135_4585.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___135_4585.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___135_4585.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___135_4585.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___135_4585.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___135_4585.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___135_4585.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___135_4585.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___135_4585.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___135_4585.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___135_4585.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___135_4585.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___135_4585.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___135_4585.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___135_4585.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___135_4585.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___135_4585.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___135_4585.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___135_4585.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___135_4585.FStar_TypeChecker_Env.is_native_tactic)
                             }) uu____4584 FStar_Syntax_Syntax.U_unknown in
                        let uu____4586 =
                          let uu____4587 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4587 in
                        FStar_Util.Inl uu____4586
                    | FStar_Util.Inr (eff_name,uu____4594) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4625 =
                        let uu____4626 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4626 in
                      FStar_All.pipe_right uu____4625
                        (fun _0_41  -> Some _0_41)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4638 =
                        let uu____4639 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4639 FStar_Pervasives.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4647 =
                          let uu____4648 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4648 in
                        FStar_All.pipe_right uu____4647
                          (fun _0_42  -> Some _0_42)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4652 =
                             let uu____4653 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4653 in
                           FStar_All.pipe_right uu____4652
                             (fun _0_43  -> Some _0_43))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4664 =
                         let uu____4665 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4665 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4664);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4680 =
                       (is_impure lc1) &&
                         (let uu____4681 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4681) in
                     if uu____4680
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4686 = encode_binders None bs1 env in
                        match uu____4686 with
                        | (vars,guards,envbody,decls,uu____4701) ->
                            let uu____4708 =
                              let uu____4716 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4716
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4708 with
                             | (lc2,body2) ->
                                 let uu____4741 = encode_term body2 envbody in
                                 (match uu____4741 with
                                  | (body3,decls') ->
                                      let uu____4748 =
                                        let uu____4753 = codomain_eff lc2 in
                                        match uu____4753 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4765 =
                                              encode_term tfun env in
                                            (match uu____4765 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4748 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4784 =
                                               let uu____4790 =
                                                 let uu____4791 =
                                                   let uu____4794 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4794, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4791 in
                                               ([], vars, uu____4790) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4784 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4802 =
                                                   let uu____4804 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4804 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4802 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4815 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4815 with
                                            | Some cache_entry ->
                                                let uu____4820 =
                                                  let uu____4821 =
                                                    let uu____4825 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4825) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4821 in
                                                (uu____4820,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | None  ->
                                                let uu____4831 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4831 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4838 =
                                                         let uu____4839 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4839 =
                                                           cache_size in
                                                       if uu____4838
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
                                                         let uu____4850 =
                                                           let uu____4851 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4851 in
                                                         varops.mk_unique
                                                           uu____4850 in
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
                                                       let uu____4856 =
                                                         let uu____4860 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4860) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4856 in
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
                                                           let uu____4872 =
                                                             let uu____4873 =
                                                               let uu____4877
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4877,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4873 in
                                                           [uu____4872] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4885 =
                                                         let uu____4889 =
                                                           let uu____4890 =
                                                             let uu____4896 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4896) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4890 in
                                                         (uu____4889,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4885 in
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
                                                     ((let uu____4906 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4906);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4908,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4909;
                          FStar_Syntax_Syntax.lbunivs = uu____4910;
                          FStar_Syntax_Syntax.lbtyp = uu____4911;
                          FStar_Syntax_Syntax.lbeff = uu____4912;
                          FStar_Syntax_Syntax.lbdef = uu____4913;_}::uu____4914),uu____4915)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4933;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4935;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4951 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4964 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4964, [decl_e])))
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
              let uu____5006 = encode_term e1 env in
              match uu____5006 with
              | (ee1,decls1) ->
                  let uu____5013 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____5013 with
                   | (xs,e21) ->
                       let uu____5027 = FStar_List.hd xs in
                       (match uu____5027 with
                        | (x1,uu____5035) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____5037 = encode_body e21 env' in
                            (match uu____5037 with
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
            let uu____5059 =
              let uu____5063 =
                let uu____5064 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____5064 in
              gen_term_var env uu____5063 in
            match uu____5059 with
            | (scrsym,scr',env1) ->
                let uu____5074 = encode_term e env1 in
                (match uu____5074 with
                 | (scr,decls) ->
                     let uu____5081 =
                       let encode_branch b uu____5097 =
                         match uu____5097 with
                         | (else_case,decls1) ->
                             let uu____5108 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____5108 with
                              | (p,w,br) ->
                                  let uu____5129 = encode_pat env1 p in
                                  (match uu____5129 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____5149  ->
                                                   match uu____5149 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____5154 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____5169 =
                                               encode_term w1 env2 in
                                             (match uu____5169 with
                                              | (w2,decls2) ->
                                                  let uu____5177 =
                                                    let uu____5178 =
                                                      let uu____5181 =
                                                        let uu____5182 =
                                                          let uu____5185 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____5185) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____5182 in
                                                      (guard, uu____5181) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____5178 in
                                                  (uu____5177, decls2)) in
                                       (match uu____5154 with
                                        | (guard1,decls2) ->
                                            let uu____5193 =
                                              encode_br br env2 in
                                            (match uu____5193 with
                                             | (br1,decls3) ->
                                                 let uu____5201 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____5201,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____5081 with
                      | (match_tm,decls1) ->
                          let uu____5212 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____5212, decls1)))
and encode_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____5234 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5234
       then
         let uu____5235 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5235
       else ());
      (let uu____5237 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5237 with
       | (vars,pat_term) ->
           let uu____5247 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5270  ->
                     fun v1  ->
                       match uu____5270 with
                       | (env1,vars1) ->
                           let uu____5298 = gen_term_var env1 v1 in
                           (match uu____5298 with
                            | (xx,uu____5310,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____5247 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5357 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5358 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5359 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5365 =
                        let uu____5368 = encode_const c in
                        (scrutinee, uu____5368) in
                      FStar_SMTEncoding_Util.mkEq uu____5365
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5387 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5387 with
                        | (uu____5391,uu____5392::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5394 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5415  ->
                                  match uu____5415 with
                                  | (arg,uu____5421) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5431 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5431)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5451) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5470 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5485 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5507  ->
                                  match uu____5507 with
                                  | (arg,uu____5516) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5526 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5526)) in
                      FStar_All.pipe_right uu____5485 FStar_List.flatten in
                let pat_term1 uu____5542 = encode_term pat_term env1 in
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
      let uu____5549 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5564  ->
                fun uu____5565  ->
                  match (uu____5564, uu____5565) with
                  | ((tms,decls),(t,uu____5585)) ->
                      let uu____5596 = encode_term t env in
                      (match uu____5596 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5549 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5630 = FStar_Syntax_Util.list_elements e in
        match uu____5630 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5645 =
          let uu____5655 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5655 FStar_Syntax_Util.head_and_args in
        match uu____5645 with
        | (head1,args) ->
            let uu____5683 =
              let uu____5691 =
                let uu____5692 = FStar_Syntax_Util.un_uinst head1 in
                uu____5692.FStar_Syntax_Syntax.n in
              (uu____5691, args) in
            (match uu____5683 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5703,uu____5704)::(e,uu____5706)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> e
             | uu____5732 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____5759 =
            let uu____5769 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5769 FStar_Syntax_Util.head_and_args in
          match uu____5759 with
          | (head1,args) ->
              let uu____5798 =
                let uu____5806 =
                  let uu____5807 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5807.FStar_Syntax_Syntax.n in
                (uu____5806, args) in
              (match uu____5798 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5820)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5840 -> None) in
        match elts with
        | t1::[] ->
            let uu____5855 = smt_pat_or1 t1 in
            (match uu____5855 with
             | Some e ->
                 let uu____5868 = list_elements1 e in
                 FStar_All.pipe_right uu____5868
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5879 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5879
                           (FStar_List.map one_pat)))
             | uu____5887 ->
                 let uu____5891 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5891])
        | uu____5907 ->
            let uu____5909 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5909] in
      let uu____5925 =
        let uu____5938 =
          let uu____5939 = FStar_Syntax_Subst.compress t in
          uu____5939.FStar_Syntax_Syntax.n in
        match uu____5938 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5966 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5966 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5995;
                        FStar_Syntax_Syntax.effect_name = uu____5996;
                        FStar_Syntax_Syntax.result_typ = uu____5997;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5999)::(post,uu____6001)::(pats,uu____6003)::[];
                        FStar_Syntax_Syntax.flags = uu____6004;_}
                      ->
                      let uu____6036 = lemma_pats pats in
                      (binders1, pre, post, uu____6036)
                  | uu____6049 -> failwith "impos"))
        | uu____6062 -> failwith "Impos" in
      match uu____5925 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___136_6098 = env in
            {
              bindings = (uu___136_6098.bindings);
              depth = (uu___136_6098.depth);
              tcenv = (uu___136_6098.tcenv);
              warn = (uu___136_6098.warn);
              cache = (uu___136_6098.cache);
              nolabels = (uu___136_6098.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___136_6098.encode_non_total_function_typ);
              current_module_name = (uu___136_6098.current_module_name)
            } in
          let uu____6099 = encode_binders None binders env1 in
          (match uu____6099 with
           | (vars,guards,env2,decls,uu____6114) ->
               let uu____6121 =
                 let uu____6128 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____6150 =
                             let uu____6155 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____6155 FStar_List.unzip in
                           match uu____6150 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____6128 FStar_List.unzip in
               (match uu____6121 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___137_6213 = env2 in
                      {
                        bindings = (uu___137_6213.bindings);
                        depth = (uu___137_6213.depth);
                        tcenv = (uu___137_6213.tcenv);
                        warn = (uu___137_6213.warn);
                        cache = (uu___137_6213.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___137_6213.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___137_6213.encode_non_total_function_typ);
                        current_module_name =
                          (uu___137_6213.current_module_name)
                      } in
                    let uu____6214 =
                      let uu____6217 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6217 env3 in
                    (match uu____6214 with
                     | (pre1,decls'') ->
                         let uu____6222 =
                           let uu____6225 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6225 env3 in
                         (match uu____6222 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6232 =
                                let uu____6233 =
                                  let uu____6239 =
                                    let uu____6240 =
                                      let uu____6243 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6243, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6240 in
                                  (pats, vars, uu____6239) in
                                FStar_SMTEncoding_Util.mkForall uu____6233 in
                              (uu____6232, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6256 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6256
        then
          let uu____6257 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6258 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6257 uu____6258
        else () in
      let enc f r l =
        let uu____6285 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6298 = encode_term (fst x) env in
                 match uu____6298 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6285 with
        | (decls,args) ->
            let uu____6315 =
              let uu___138_6316 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___138_6316.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___138_6316.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6315, decls) in
      let const_op f r uu____6341 = let uu____6350 = f r in (uu____6350, []) in
      let un_op f l =
        let uu____6366 = FStar_List.hd l in FStar_All.pipe_left f uu____6366 in
      let bin_op f uu___111_6379 =
        match uu___111_6379 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6387 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6414 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6423  ->
                 match uu____6423 with
                 | (t,uu____6431) ->
                     let uu____6432 = encode_formula t env in
                     (match uu____6432 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6414 with
        | (decls,phis) ->
            let uu____6449 =
              let uu___139_6450 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6450.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6450.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6449, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____6489  ->
               match uu____6489 with
               | (a,q) ->
                   (match q with
                    | Some (FStar_Syntax_Syntax.Implicit uu____6503) -> false
                    | uu____6504 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____6517 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____6517
        else
          (let uu____6532 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____6532 r rf) in
      let mk_imp1 r uu___112_6551 =
        match uu___112_6551 with
        | (lhs,uu____6555)::(rhs,uu____6557)::[] ->
            let uu____6578 = encode_formula rhs env in
            (match uu____6578 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6587) ->
                      (l1, decls1)
                  | uu____6590 ->
                      let uu____6591 = encode_formula lhs env in
                      (match uu____6591 with
                       | (l2,decls2) ->
                           let uu____6598 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6598, (FStar_List.append decls1 decls2)))))
        | uu____6600 -> failwith "impossible" in
      let mk_ite r uu___113_6615 =
        match uu___113_6615 with
        | (guard,uu____6619)::(_then,uu____6621)::(_else,uu____6623)::[] ->
            let uu____6652 = encode_formula guard env in
            (match uu____6652 with
             | (g,decls1) ->
                 let uu____6659 = encode_formula _then env in
                 (match uu____6659 with
                  | (t,decls2) ->
                      let uu____6666 = encode_formula _else env in
                      (match uu____6666 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6675 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6694 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6694 in
      let connectives =
        let uu____6706 =
          let uu____6715 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6715) in
        let uu____6728 =
          let uu____6738 =
            let uu____6747 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6747) in
          let uu____6760 =
            let uu____6770 =
              let uu____6780 =
                let uu____6789 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6789) in
              let uu____6802 =
                let uu____6812 =
                  let uu____6822 =
                    let uu____6831 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6831) in
                  [uu____6822;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6812 in
              uu____6780 :: uu____6802 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6770 in
          uu____6738 :: uu____6760 in
        uu____6706 :: uu____6728 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____7047 = encode_formula phi' env in
            (match uu____7047 with
             | (phi2,decls) ->
                 let uu____7054 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____7054, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____7055 ->
            let uu____7060 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____7060 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____7089 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____7089 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____7097;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____7099;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____7115 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____7115 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____7147::(x,uu____7149)::(t,uu____7151)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____7185 = encode_term x env in
                 (match uu____7185 with
                  | (x1,decls) ->
                      let uu____7192 = encode_term t env in
                      (match uu____7192 with
                       | (t1,decls') ->
                           let uu____7199 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____7199, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____7203)::(msg,uu____7205)::(phi2,uu____7207)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____7241 =
                   let uu____7244 =
                     let uu____7245 = FStar_Syntax_Subst.compress r in
                     uu____7245.FStar_Syntax_Syntax.n in
                   let uu____7248 =
                     let uu____7249 = FStar_Syntax_Subst.compress msg in
                     uu____7249.FStar_Syntax_Syntax.n in
                   (uu____7244, uu____7248) in
                 (match uu____7241 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7256))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____7272 -> fallback phi2)
             | uu____7275 when head_redex env head2 ->
                 let uu____7283 = whnf env phi1 in
                 encode_formula uu____7283 env
             | uu____7284 ->
                 let uu____7292 = encode_term phi1 env in
                 (match uu____7292 with
                  | (tt,decls) ->
                      let uu____7299 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___140_7300 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___140_7300.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___140_7300.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7299, decls)))
        | uu____7303 ->
            let uu____7304 = encode_term phi1 env in
            (match uu____7304 with
             | (tt,decls) ->
                 let uu____7311 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___141_7312 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___141_7312.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___141_7312.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7311, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7339 = encode_binders None bs env1 in
        match uu____7339 with
        | (vars,guards,env2,decls,uu____7361) ->
            let uu____7368 =
              let uu____7375 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7398 =
                          let uu____7403 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7417  ->
                                    match uu____7417 with
                                    | (t,uu____7423) ->
                                        encode_term t
                                          (let uu___142_7424 = env2 in
                                           {
                                             bindings =
                                               (uu___142_7424.bindings);
                                             depth = (uu___142_7424.depth);
                                             tcenv = (uu___142_7424.tcenv);
                                             warn = (uu___142_7424.warn);
                                             cache = (uu___142_7424.cache);
                                             nolabels =
                                               (uu___142_7424.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___142_7424.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___142_7424.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7403 FStar_List.unzip in
                        match uu____7398 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7375 FStar_List.unzip in
            (match uu____7368 with
             | (pats,decls') ->
                 let uu____7476 = encode_formula body env2 in
                 (match uu____7476 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7495;
                             FStar_SMTEncoding_Term.rng = uu____7496;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7504 -> guards in
                      let uu____7507 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7507, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7541  ->
                   match uu____7541 with
                   | (x,uu____7545) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7551 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7557 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7557) uu____7551 tl1 in
             let uu____7559 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7571  ->
                       match uu____7571 with
                       | (b,uu____7575) ->
                           let uu____7576 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7576)) in
             (match uu____7559 with
              | None  -> ()
              | Some (x,uu____7580) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7590 =
                    let uu____7591 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7591 in
                  FStar_Errors.warn pos uu____7590) in
       let uu____7592 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7592 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7598 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7634  ->
                     match uu____7634 with
                     | (l,uu____7644) -> FStar_Ident.lid_equals op l)) in
           (match uu____7598 with
            | None  -> fallback phi1
            | Some (uu____7667,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7696 = encode_q_body env vars pats body in
             match uu____7696 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7722 =
                     let uu____7728 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7728) in
                   FStar_SMTEncoding_Term.mkForall uu____7722
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7740 = encode_q_body env vars pats body in
             match uu____7740 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7765 =
                   let uu____7766 =
                     let uu____7772 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7772) in
                   FStar_SMTEncoding_Term.mkExists uu____7766
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7765, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7831 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7831 with
  | (asym,a) ->
      let uu____7836 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7836 with
       | (xsym,x) ->
           let uu____7841 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7841 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7871 =
                      let uu____7877 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____7877, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7871 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7892 =
                      let uu____7896 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7896) in
                    FStar_SMTEncoding_Util.mkApp uu____7892 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7904 =
                    let uu____7906 =
                      let uu____7908 =
                        let uu____7910 =
                          let uu____7911 =
                            let uu____7915 =
                              let uu____7916 =
                                let uu____7922 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7922) in
                              FStar_SMTEncoding_Util.mkForall uu____7916 in
                            (uu____7915, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7911 in
                        let uu____7931 =
                          let uu____7933 =
                            let uu____7934 =
                              let uu____7938 =
                                let uu____7939 =
                                  let uu____7945 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7945) in
                                FStar_SMTEncoding_Util.mkForall uu____7939 in
                              (uu____7938,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7934 in
                          [uu____7933] in
                        uu____7910 :: uu____7931 in
                      xtok_decl :: uu____7908 in
                    xname_decl :: uu____7906 in
                  (xtok1, uu____7904) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7994 =
                    let uu____8002 =
                      let uu____8008 =
                        let uu____8009 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____8009 in
                      quant axy uu____8008 in
                    (FStar_Syntax_Const.op_Eq, uu____8002) in
                  let uu____8015 =
                    let uu____8024 =
                      let uu____8032 =
                        let uu____8038 =
                          let uu____8039 =
                            let uu____8040 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____8040 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____8039 in
                        quant axy uu____8038 in
                      (FStar_Syntax_Const.op_notEq, uu____8032) in
                    let uu____8046 =
                      let uu____8055 =
                        let uu____8063 =
                          let uu____8069 =
                            let uu____8070 =
                              let uu____8071 =
                                let uu____8074 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8075 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____8074, uu____8075) in
                              FStar_SMTEncoding_Util.mkLT uu____8071 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____8070 in
                          quant xy uu____8069 in
                        (FStar_Syntax_Const.op_LT, uu____8063) in
                      let uu____8081 =
                        let uu____8090 =
                          let uu____8098 =
                            let uu____8104 =
                              let uu____8105 =
                                let uu____8106 =
                                  let uu____8109 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____8110 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____8109, uu____8110) in
                                FStar_SMTEncoding_Util.mkLTE uu____8106 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____8105 in
                            quant xy uu____8104 in
                          (FStar_Syntax_Const.op_LTE, uu____8098) in
                        let uu____8116 =
                          let uu____8125 =
                            let uu____8133 =
                              let uu____8139 =
                                let uu____8140 =
                                  let uu____8141 =
                                    let uu____8144 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____8145 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____8144, uu____8145) in
                                  FStar_SMTEncoding_Util.mkGT uu____8141 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____8140 in
                              quant xy uu____8139 in
                            (FStar_Syntax_Const.op_GT, uu____8133) in
                          let uu____8151 =
                            let uu____8160 =
                              let uu____8168 =
                                let uu____8174 =
                                  let uu____8175 =
                                    let uu____8176 =
                                      let uu____8179 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____8180 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____8179, uu____8180) in
                                    FStar_SMTEncoding_Util.mkGTE uu____8176 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____8175 in
                                quant xy uu____8174 in
                              (FStar_Syntax_Const.op_GTE, uu____8168) in
                            let uu____8186 =
                              let uu____8195 =
                                let uu____8203 =
                                  let uu____8209 =
                                    let uu____8210 =
                                      let uu____8211 =
                                        let uu____8214 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____8215 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____8214, uu____8215) in
                                      FStar_SMTEncoding_Util.mkSub uu____8211 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8210 in
                                  quant xy uu____8209 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____8203) in
                              let uu____8221 =
                                let uu____8230 =
                                  let uu____8238 =
                                    let uu____8244 =
                                      let uu____8245 =
                                        let uu____8246 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8246 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8245 in
                                    quant qx uu____8244 in
                                  (FStar_Syntax_Const.op_Minus, uu____8238) in
                                let uu____8252 =
                                  let uu____8261 =
                                    let uu____8269 =
                                      let uu____8275 =
                                        let uu____8276 =
                                          let uu____8277 =
                                            let uu____8280 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8281 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8280, uu____8281) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8277 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8276 in
                                      quant xy uu____8275 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8269) in
                                  let uu____8287 =
                                    let uu____8296 =
                                      let uu____8304 =
                                        let uu____8310 =
                                          let uu____8311 =
                                            let uu____8312 =
                                              let uu____8315 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8316 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8315, uu____8316) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8312 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8311 in
                                        quant xy uu____8310 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8304) in
                                    let uu____8322 =
                                      let uu____8331 =
                                        let uu____8339 =
                                          let uu____8345 =
                                            let uu____8346 =
                                              let uu____8347 =
                                                let uu____8350 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8351 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8350, uu____8351) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8347 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8346 in
                                          quant xy uu____8345 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8339) in
                                      let uu____8357 =
                                        let uu____8366 =
                                          let uu____8374 =
                                            let uu____8380 =
                                              let uu____8381 =
                                                let uu____8382 =
                                                  let uu____8385 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8386 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8385, uu____8386) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8382 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8381 in
                                            quant xy uu____8380 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8374) in
                                        let uu____8392 =
                                          let uu____8401 =
                                            let uu____8409 =
                                              let uu____8415 =
                                                let uu____8416 =
                                                  let uu____8417 =
                                                    let uu____8420 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8421 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8420, uu____8421) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8417 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8416 in
                                              quant xy uu____8415 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8409) in
                                          let uu____8427 =
                                            let uu____8436 =
                                              let uu____8444 =
                                                let uu____8450 =
                                                  let uu____8451 =
                                                    let uu____8452 =
                                                      let uu____8455 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8456 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8455,
                                                        uu____8456) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8452 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8451 in
                                                quant xy uu____8450 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8444) in
                                            let uu____8462 =
                                              let uu____8471 =
                                                let uu____8479 =
                                                  let uu____8485 =
                                                    let uu____8486 =
                                                      let uu____8487 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8487 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8486 in
                                                  quant qx uu____8485 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8479) in
                                              [uu____8471] in
                                            uu____8436 :: uu____8462 in
                                          uu____8401 :: uu____8427 in
                                        uu____8366 :: uu____8392 in
                                      uu____8331 :: uu____8357 in
                                    uu____8296 :: uu____8322 in
                                  uu____8261 :: uu____8287 in
                                uu____8230 :: uu____8252 in
                              uu____8195 :: uu____8221 in
                            uu____8160 :: uu____8186 in
                          uu____8125 :: uu____8151 in
                        uu____8090 :: uu____8116 in
                      uu____8055 :: uu____8081 in
                    uu____8024 :: uu____8046 in
                  uu____7994 :: uu____8015 in
                let mk1 l v1 =
                  let uu____8615 =
                    let uu____8620 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8652  ->
                              match uu____8652 with
                              | (l',uu____8661) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8620
                      (FStar_Option.map
                         (fun uu____8694  ->
                            match uu____8694 with | (uu____8705,b) -> b v1)) in
                  FStar_All.pipe_right uu____8615 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8746  ->
                          match uu____8746 with
                          | (l',uu____8755) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8784 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8784 with
        | (xxsym,xx) ->
            let uu____8789 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8789 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8797 =
                   let uu____8801 =
                     let uu____8802 =
                       let uu____8808 =
                         let uu____8809 =
                           let uu____8812 =
                             let uu____8813 =
                               let uu____8816 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8816) in
                             FStar_SMTEncoding_Util.mkEq uu____8813 in
                           (xx_has_type, uu____8812) in
                         FStar_SMTEncoding_Util.mkImp uu____8809 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8808) in
                     FStar_SMTEncoding_Util.mkForall uu____8802 in
                   let uu____8829 =
                     let uu____8830 =
                       let uu____8831 =
                         let uu____8832 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8832 in
                       Prims.strcat module_name uu____8831 in
                     varops.mk_unique uu____8830 in
                   (uu____8801, (Some "pretyping"), uu____8829) in
                 FStar_SMTEncoding_Util.mkAssume uu____8797)
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
    let uu____8866 =
      let uu____8867 =
        let uu____8871 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8871, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8867 in
    let uu____8873 =
      let uu____8875 =
        let uu____8876 =
          let uu____8880 =
            let uu____8881 =
              let uu____8887 =
                let uu____8888 =
                  let uu____8891 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8891) in
                FStar_SMTEncoding_Util.mkImp uu____8888 in
              ([[typing_pred]], [xx], uu____8887) in
            mkForall_fuel uu____8881 in
          (uu____8880, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8876 in
      [uu____8875] in
    uu____8866 :: uu____8873 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8919 =
      let uu____8920 =
        let uu____8924 =
          let uu____8925 =
            let uu____8931 =
              let uu____8934 =
                let uu____8936 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8936] in
              [uu____8934] in
            let uu____8939 =
              let uu____8940 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8940 tt in
            (uu____8931, [bb], uu____8939) in
          FStar_SMTEncoding_Util.mkForall uu____8925 in
        (uu____8924, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8920 in
    let uu____8951 =
      let uu____8953 =
        let uu____8954 =
          let uu____8958 =
            let uu____8959 =
              let uu____8965 =
                let uu____8966 =
                  let uu____8969 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8969) in
                FStar_SMTEncoding_Util.mkImp uu____8966 in
              ([[typing_pred]], [xx], uu____8965) in
            mkForall_fuel uu____8959 in
          (uu____8958, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8954 in
      [uu____8953] in
    uu____8919 :: uu____8951 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____9003 =
        let uu____9004 =
          let uu____9008 =
            let uu____9010 =
              let uu____9012 =
                let uu____9014 = FStar_SMTEncoding_Term.boxInt a in
                let uu____9015 =
                  let uu____9017 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____9017] in
                uu____9014 :: uu____9015 in
              tt :: uu____9012 in
            tt :: uu____9010 in
          ("Prims.Precedes", uu____9008) in
        FStar_SMTEncoding_Util.mkApp uu____9004 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9003 in
    let precedes_y_x =
      let uu____9020 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9020 in
    let uu____9022 =
      let uu____9023 =
        let uu____9027 =
          let uu____9028 =
            let uu____9034 =
              let uu____9037 =
                let uu____9039 = FStar_SMTEncoding_Term.boxInt b in
                [uu____9039] in
              [uu____9037] in
            let uu____9042 =
              let uu____9043 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____9043 tt in
            (uu____9034, [bb], uu____9042) in
          FStar_SMTEncoding_Util.mkForall uu____9028 in
        (uu____9027, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9023 in
    let uu____9054 =
      let uu____9056 =
        let uu____9057 =
          let uu____9061 =
            let uu____9062 =
              let uu____9068 =
                let uu____9069 =
                  let uu____9072 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____9072) in
                FStar_SMTEncoding_Util.mkImp uu____9069 in
              ([[typing_pred]], [xx], uu____9068) in
            mkForall_fuel uu____9062 in
          (uu____9061, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9057 in
      let uu____9085 =
        let uu____9087 =
          let uu____9088 =
            let uu____9092 =
              let uu____9093 =
                let uu____9099 =
                  let uu____9100 =
                    let uu____9103 =
                      let uu____9104 =
                        let uu____9106 =
                          let uu____9108 =
                            let uu____9110 =
                              let uu____9111 =
                                let uu____9114 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____9115 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____9114, uu____9115) in
                              FStar_SMTEncoding_Util.mkGT uu____9111 in
                            let uu____9116 =
                              let uu____9118 =
                                let uu____9119 =
                                  let uu____9122 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____9123 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____9122, uu____9123) in
                                FStar_SMTEncoding_Util.mkGTE uu____9119 in
                              let uu____9124 =
                                let uu____9126 =
                                  let uu____9127 =
                                    let uu____9130 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____9131 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____9130, uu____9131) in
                                  FStar_SMTEncoding_Util.mkLT uu____9127 in
                                [uu____9126] in
                              uu____9118 :: uu____9124 in
                            uu____9110 :: uu____9116 in
                          typing_pred_y :: uu____9108 in
                        typing_pred :: uu____9106 in
                      FStar_SMTEncoding_Util.mk_and_l uu____9104 in
                    (uu____9103, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____9100 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____9099) in
              mkForall_fuel uu____9093 in
            (uu____9092, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____9088 in
        [uu____9087] in
      uu____9056 :: uu____9085 in
    uu____9022 :: uu____9054 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9161 =
      let uu____9162 =
        let uu____9166 =
          let uu____9167 =
            let uu____9173 =
              let uu____9176 =
                let uu____9178 = FStar_SMTEncoding_Term.boxString b in
                [uu____9178] in
              [uu____9176] in
            let uu____9181 =
              let uu____9182 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____9182 tt in
            (uu____9173, [bb], uu____9181) in
          FStar_SMTEncoding_Util.mkForall uu____9167 in
        (uu____9166, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9162 in
    let uu____9193 =
      let uu____9195 =
        let uu____9196 =
          let uu____9200 =
            let uu____9201 =
              let uu____9207 =
                let uu____9208 =
                  let uu____9211 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____9211) in
                FStar_SMTEncoding_Util.mkImp uu____9208 in
              ([[typing_pred]], [xx], uu____9207) in
            mkForall_fuel uu____9201 in
          (uu____9200, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9196 in
      [uu____9195] in
    uu____9161 :: uu____9193 in
  let mk_ref1 env reft_name uu____9233 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____9244 =
        let uu____9248 =
          let uu____9250 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9250] in
        (reft_name, uu____9248) in
      FStar_SMTEncoding_Util.mkApp uu____9244 in
    let refb =
      let uu____9253 =
        let uu____9257 =
          let uu____9259 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9259] in
        (reft_name, uu____9257) in
      FStar_SMTEncoding_Util.mkApp uu____9253 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9263 =
      let uu____9264 =
        let uu____9268 =
          let uu____9269 =
            let uu____9275 =
              let uu____9276 =
                let uu____9279 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9279) in
              FStar_SMTEncoding_Util.mkImp uu____9276 in
            ([[typing_pred]], [xx; aa], uu____9275) in
          mkForall_fuel uu____9269 in
        (uu____9268, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9264 in
    [uu____9263] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9319 =
      let uu____9320 =
        let uu____9324 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9324, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9320 in
    [uu____9319] in
  let mk_and_interp env conj uu____9335 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9352 =
      let uu____9353 =
        let uu____9357 =
          let uu____9358 =
            let uu____9364 =
              let uu____9365 =
                let uu____9368 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9368, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9365 in
            ([[l_and_a_b]], [aa; bb], uu____9364) in
          FStar_SMTEncoding_Util.mkForall uu____9358 in
        (uu____9357, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9353 in
    [uu____9352] in
  let mk_or_interp env disj uu____9392 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9409 =
      let uu____9410 =
        let uu____9414 =
          let uu____9415 =
            let uu____9421 =
              let uu____9422 =
                let uu____9425 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9425, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9422 in
            ([[l_or_a_b]], [aa; bb], uu____9421) in
          FStar_SMTEncoding_Util.mkForall uu____9415 in
        (uu____9414, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9410 in
    [uu____9409] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9466 =
      let uu____9467 =
        let uu____9471 =
          let uu____9472 =
            let uu____9478 =
              let uu____9479 =
                let uu____9482 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9482, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9479 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9478) in
          FStar_SMTEncoding_Util.mkForall uu____9472 in
        (uu____9471, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9467 in
    [uu____9466] in
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
    let uu____9529 =
      let uu____9530 =
        let uu____9534 =
          let uu____9535 =
            let uu____9541 =
              let uu____9542 =
                let uu____9545 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9545, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9542 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9541) in
          FStar_SMTEncoding_Util.mkForall uu____9535 in
        (uu____9534, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9530 in
    [uu____9529] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9590 =
      let uu____9591 =
        let uu____9595 =
          let uu____9596 =
            let uu____9602 =
              let uu____9603 =
                let uu____9606 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9606, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9603 in
            ([[l_imp_a_b]], [aa; bb], uu____9602) in
          FStar_SMTEncoding_Util.mkForall uu____9596 in
        (uu____9595, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9591 in
    [uu____9590] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9647 =
      let uu____9648 =
        let uu____9652 =
          let uu____9653 =
            let uu____9659 =
              let uu____9660 =
                let uu____9663 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9663, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9660 in
            ([[l_iff_a_b]], [aa; bb], uu____9659) in
          FStar_SMTEncoding_Util.mkForall uu____9653 in
        (uu____9652, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9648 in
    [uu____9647] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9697 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9697 in
    let uu____9699 =
      let uu____9700 =
        let uu____9704 =
          let uu____9705 =
            let uu____9711 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9711) in
          FStar_SMTEncoding_Util.mkForall uu____9705 in
        (uu____9704, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9700 in
    [uu____9699] in
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
      let uu____9751 =
        let uu____9755 =
          let uu____9757 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9757] in
        ("Valid", uu____9755) in
      FStar_SMTEncoding_Util.mkApp uu____9751 in
    let uu____9759 =
      let uu____9760 =
        let uu____9764 =
          let uu____9765 =
            let uu____9771 =
              let uu____9772 =
                let uu____9775 =
                  let uu____9776 =
                    let uu____9782 =
                      let uu____9785 =
                        let uu____9787 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9787] in
                      [uu____9785] in
                    let uu____9790 =
                      let uu____9791 =
                        let uu____9794 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9794, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9791 in
                    (uu____9782, [xx1], uu____9790) in
                  FStar_SMTEncoding_Util.mkForall uu____9776 in
                (uu____9775, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9772 in
            ([[l_forall_a_b]], [aa; bb], uu____9771) in
          FStar_SMTEncoding_Util.mkForall uu____9765 in
        (uu____9764, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9760 in
    [uu____9759] in
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
      let uu____9845 =
        let uu____9849 =
          let uu____9851 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9851] in
        ("Valid", uu____9849) in
      FStar_SMTEncoding_Util.mkApp uu____9845 in
    let uu____9853 =
      let uu____9854 =
        let uu____9858 =
          let uu____9859 =
            let uu____9865 =
              let uu____9866 =
                let uu____9869 =
                  let uu____9870 =
                    let uu____9876 =
                      let uu____9879 =
                        let uu____9881 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9881] in
                      [uu____9879] in
                    let uu____9884 =
                      let uu____9885 =
                        let uu____9888 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9888, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9885 in
                    (uu____9876, [xx1], uu____9884) in
                  FStar_SMTEncoding_Util.mkExists uu____9870 in
                (uu____9869, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9866 in
            ([[l_exists_a_b]], [aa; bb], uu____9865) in
          FStar_SMTEncoding_Util.mkForall uu____9859 in
        (uu____9858, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9854 in
    [uu____9853] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9924 =
      let uu____9925 =
        let uu____9929 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9930 = varops.mk_unique "typing_range_const" in
        (uu____9929, (Some "Range_const typing"), uu____9930) in
      FStar_SMTEncoding_Util.mkAssume uu____9925 in
    [uu____9924] in
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
          let uu____10192 =
            FStar_Util.find_opt
              (fun uu____10210  ->
                 match uu____10210 with
                 | (l,uu____10220) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____10192 with
          | None  -> []
          | Some (uu____10242,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10282 = encode_function_type_as_formula t env in
        match uu____10282 with
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
            let uu____10319 =
              (let uu____10320 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10320) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10319
            then
              let uu____10324 = new_term_constant_and_tok_from_lid env lid in
              match uu____10324 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10336 =
                      let uu____10337 = FStar_Syntax_Subst.compress t_norm in
                      uu____10337.FStar_Syntax_Syntax.n in
                    match uu____10336 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10342) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10359  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10362 -> [] in
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
              (let uu____10371 = prims.is lid in
               if uu____10371
               then
                 let vname = varops.new_fvar lid in
                 let uu____10376 = prims.mk lid vname in
                 match uu____10376 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10391 =
                    let uu____10397 = curried_arrow_formals_comp t_norm in
                    match uu____10397 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10408 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10408
                          then
                            let uu____10409 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___143_10410 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___143_10410.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___143_10410.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___143_10410.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___143_10410.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___143_10410.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___143_10410.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___143_10410.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___143_10410.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___143_10410.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___143_10410.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___143_10410.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___143_10410.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___143_10410.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___143_10410.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___143_10410.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___143_10410.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___143_10410.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___143_10410.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___143_10410.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___143_10410.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___143_10410.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___143_10410.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___143_10410.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___143_10410.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___143_10410.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___143_10410.FStar_TypeChecker_Env.is_native_tactic)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10409
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10417 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10417)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10391 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10444 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10444 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10457 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___114_10481  ->
                                     match uu___114_10481 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10484 =
                                           FStar_Util.prefix vars in
                                         (match uu____10484 with
                                          | (uu____10495,(xxsym,uu____10497))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10507 =
                                                let uu____10508 =
                                                  let uu____10512 =
                                                    let uu____10513 =
                                                      let uu____10519 =
                                                        let uu____10520 =
                                                          let uu____10523 =
                                                            let uu____10524 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10524 in
                                                          (vapp, uu____10523) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10520 in
                                                      ([[vapp]], vars,
                                                        uu____10519) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10513 in
                                                  (uu____10512,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10508 in
                                              [uu____10507])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10535 =
                                           FStar_Util.prefix vars in
                                         (match uu____10535 with
                                          | (uu____10546,(xxsym,uu____10548))
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
                                              let uu____10562 =
                                                let uu____10563 =
                                                  let uu____10567 =
                                                    let uu____10568 =
                                                      let uu____10574 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10574) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10568 in
                                                  (uu____10567,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10563 in
                                              [uu____10562])
                                     | uu____10583 -> [])) in
                           let uu____10584 = encode_binders None formals env1 in
                           (match uu____10584 with
                            | (vars,guards,env',decls1,uu____10600) ->
                                let uu____10607 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10612 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10612, decls1)
                                  | Some p ->
                                      let uu____10614 = encode_formula p env' in
                                      (match uu____10614 with
                                       | (g,ds) ->
                                           let uu____10621 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10621,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10607 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10630 =
                                         let uu____10634 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10634) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10630 in
                                     let uu____10639 =
                                       let vname_decl =
                                         let uu____10644 =
                                           let uu____10650 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10655  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10650,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10644 in
                                       let uu____10660 =
                                         let env2 =
                                           let uu___144_10664 = env1 in
                                           {
                                             bindings =
                                               (uu___144_10664.bindings);
                                             depth = (uu___144_10664.depth);
                                             tcenv = (uu___144_10664.tcenv);
                                             warn = (uu___144_10664.warn);
                                             cache = (uu___144_10664.cache);
                                             nolabels =
                                               (uu___144_10664.nolabels);
                                             use_zfuel_name =
                                               (uu___144_10664.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___144_10664.current_module_name)
                                           } in
                                         let uu____10665 =
                                           let uu____10666 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10666 in
                                         if uu____10665
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10660 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10676::uu____10677 ->
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
                                                   let uu____10700 =
                                                     let uu____10706 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10706) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10700 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10720 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10722 =
                                             match formals with
                                             | [] ->
                                                 let uu____10731 =
                                                   let uu____10732 =
                                                     let uu____10734 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_44  ->
                                                          Some _0_44)
                                                       uu____10734 in
                                                   push_free_var env1 lid
                                                     vname uu____10732 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10731)
                                             | uu____10737 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10742 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10742 in
                                                 let name_tok_corr =
                                                   let uu____10744 =
                                                     let uu____10748 =
                                                       let uu____10749 =
                                                         let uu____10755 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10755) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10749 in
                                                     (uu____10748,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10744 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10722 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10639 with
                                      | (decls2,env2) ->
                                          let uu____10779 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10784 =
                                              encode_term res_t1 env' in
                                            match uu____10784 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10792 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10792,
                                                  decls) in
                                          (match uu____10779 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10800 =
                                                   let uu____10804 =
                                                     let uu____10805 =
                                                       let uu____10811 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10811) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10805 in
                                                   (uu____10804,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10800 in
                                               let freshness =
                                                 let uu____10820 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10820
                                                 then
                                                   let uu____10823 =
                                                     let uu____10824 =
                                                       let uu____10830 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
                                                       let uu____10836 =
                                                         varops.next_id () in
                                                       (vname, uu____10830,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10836) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10824 in
                                                   let uu____10838 =
                                                     let uu____10840 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10840] in
                                                   uu____10823 :: uu____10838
                                                 else [] in
                                               let g =
                                                 let uu____10844 =
                                                   let uu____10846 =
                                                     let uu____10848 =
                                                       let uu____10850 =
                                                         let uu____10852 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10852 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10850 in
                                                     FStar_List.append decls3
                                                       uu____10848 in
                                                   FStar_List.append decls2
                                                     uu____10846 in
                                                 FStar_List.append decls11
                                                   uu____10844 in
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
          let uu____10878 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10878 with
          | None  ->
              let uu____10901 = encode_free_var env x t t_norm [] in
              (match uu____10901 with
               | (decls,env1) ->
                   let uu____10916 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10916 with
                    | (n1,x',uu____10935) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10947) -> ((n1, x1), [], env)
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
          let uu____10984 = encode_free_var env lid t tt quals in
          match uu____10984 with
          | (decls,env1) ->
              let uu____10995 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10995
              then
                let uu____10999 =
                  let uu____11001 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____11001 in
                (uu____10999, env1)
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
             (fun uu____11032  ->
                fun lb  ->
                  match uu____11032 with
                  | (decls,env1) ->
                      let uu____11044 =
                        let uu____11048 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____11048
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____11044 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____11063 = FStar_Syntax_Util.head_and_args t in
    match uu____11063 with
    | (hd1,args) ->
        let uu____11089 =
          let uu____11090 = FStar_Syntax_Util.un_uinst hd1 in
          uu____11090.FStar_Syntax_Syntax.n in
        (match uu____11089 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____11094,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____11107 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____11125  ->
      fun quals  ->
        match uu____11125 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____11175 = FStar_Util.first_N nbinders formals in
              match uu____11175 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11217  ->
                         fun uu____11218  ->
                           match (uu____11217, uu____11218) with
                           | ((formal,uu____11228),(binder,uu____11230)) ->
                               let uu____11235 =
                                 let uu____11240 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11240) in
                               FStar_Syntax_Syntax.NT uu____11235) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11245 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11259  ->
                              match uu____11259 with
                              | (x,i) ->
                                  let uu____11266 =
                                    let uu___145_11267 = x in
                                    let uu____11268 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___145_11267.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___145_11267.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11268
                                    } in
                                  (uu____11266, i))) in
                    FStar_All.pipe_right uu____11245
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11280 =
                      let uu____11282 =
                        let uu____11283 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11283.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_45  -> Some _0_45)
                        uu____11282 in
                    let uu____11287 =
                      let uu____11288 = FStar_Syntax_Subst.compress body in
                      let uu____11289 =
                        let uu____11290 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11290 in
                      FStar_Syntax_Syntax.extend_app_n uu____11288
                        uu____11289 in
                    uu____11287 uu____11280 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11332 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11332
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___146_11333 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___146_11333.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___146_11333.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___146_11333.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___146_11333.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___146_11333.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___146_11333.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___146_11333.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___146_11333.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___146_11333.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___146_11333.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___146_11333.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___146_11333.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___146_11333.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___146_11333.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___146_11333.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___146_11333.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___146_11333.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___146_11333.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___146_11333.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___146_11333.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___146_11333.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___146_11333.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___146_11333.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___146_11333.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___146_11333.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___146_11333.FStar_TypeChecker_Env.is_native_tactic)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11354 = FStar_Syntax_Util.abs_formals e in
                match uu____11354 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11403::uu____11404 ->
                         let uu____11412 =
                           let uu____11413 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11413.FStar_Syntax_Syntax.n in
                         (match uu____11412 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11440 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11440 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11468 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11468
                                   then
                                     let uu____11491 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11491 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11539  ->
                                                   fun uu____11540  ->
                                                     match (uu____11539,
                                                             uu____11540)
                                                     with
                                                     | ((x,uu____11550),
                                                        (b,uu____11552)) ->
                                                         let uu____11557 =
                                                           let uu____11562 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11562) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11557)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11564 =
                                            let uu____11575 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11575) in
                                          (uu____11564, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11615 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11615 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11667) ->
                              let uu____11672 =
                                let uu____11683 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____11683 in
                              (uu____11672, true)
                          | uu____11716 when Prims.op_Negation norm1 ->
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
                          | uu____11718 ->
                              let uu____11719 =
                                let uu____11720 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11721 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11720
                                  uu____11721 in
                              failwith uu____11719)
                     | uu____11734 ->
                         let uu____11735 =
                           let uu____11736 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11736.FStar_Syntax_Syntax.n in
                         (match uu____11735 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11763 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11763 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11781 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11781 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11829 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11857 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11857
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11864 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11905  ->
                            fun lb  ->
                              match uu____11905 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11956 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11956
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11959 =
                                      let uu____11967 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11967
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11959 with
                                    | (tok,decl,env2) ->
                                        let uu____11992 =
                                          let uu____11999 =
                                            let uu____12005 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____12005, tok) in
                                          uu____11999 :: toks in
                                        (uu____11992, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11864 with
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
                        | uu____12107 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____12112 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____12112 vars)
                            else
                              (let uu____12114 =
                                 let uu____12118 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____12118) in
                               FStar_SMTEncoding_Util.mkApp uu____12114) in
                      let uu____12123 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___115_12125  ->
                                 match uu___115_12125 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____12126 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____12129 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____12129))) in
                      if uu____12123
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____12149;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____12151;
                                FStar_Syntax_Syntax.lbeff = uu____12152;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____12193 =
                                 let uu____12197 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____12197 with
                                 | (tcenv',uu____12208,e_t) ->
                                     let uu____12212 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12219 -> failwith "Impossible" in
                                     (match uu____12212 with
                                      | (e1,t_norm1) ->
                                          ((let uu___149_12228 = env1 in
                                            {
                                              bindings =
                                                (uu___149_12228.bindings);
                                              depth = (uu___149_12228.depth);
                                              tcenv = tcenv';
                                              warn = (uu___149_12228.warn);
                                              cache = (uu___149_12228.cache);
                                              nolabels =
                                                (uu___149_12228.nolabels);
                                              use_zfuel_name =
                                                (uu___149_12228.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___149_12228.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___149_12228.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____12193 with
                                | (env',e1,t_norm1) ->
                                    let uu____12235 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____12235 with
                                     | ((binders,body,uu____12247,uu____12248),curry)
                                         ->
                                         ((let uu____12255 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____12255
                                           then
                                             let uu____12256 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12257 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12256 uu____12257
                                           else ());
                                          (let uu____12259 =
                                             encode_binders None binders env' in
                                           match uu____12259 with
                                           | (vars,guards,env'1,binder_decls,uu____12275)
                                               ->
                                               let body1 =
                                                 let uu____12283 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12283
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12286 =
                                                 let uu____12291 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12291
                                                 then
                                                   let uu____12297 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12298 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12297, uu____12298)
                                                 else
                                                   (let uu____12304 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12304)) in
                                               (match uu____12286 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12318 =
                                                        let uu____12322 =
                                                          let uu____12323 =
                                                            let uu____12329 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12329) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12323 in
                                                        let uu____12335 =
                                                          let uu____12337 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12337 in
                                                        (uu____12322,
                                                          uu____12335,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12318 in
                                                    let uu____12339 =
                                                      let uu____12341 =
                                                        let uu____12343 =
                                                          let uu____12345 =
                                                            let uu____12347 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12347 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12345 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12343 in
                                                      FStar_List.append
                                                        decls1 uu____12341 in
                                                    (uu____12339, env1))))))
                           | uu____12350 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12369 = varops.fresh "fuel" in
                             (uu____12369, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12372 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12411  ->
                                     fun uu____12412  ->
                                       match (uu____12411, uu____12412) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12494 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12494 in
                                           let gtok =
                                             let uu____12496 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12496 in
                                           let env3 =
                                             let uu____12498 =
                                               let uu____12500 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_46  -> Some _0_46)
                                                 uu____12500 in
                                             push_free_var env2 flid gtok
                                               uu____12498 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12372 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12586
                                 t_norm uu____12588 =
                                 match (uu____12586, uu____12588) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12615;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12616;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12633 =
                                       let uu____12637 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12637 with
                                       | (tcenv',uu____12652,e_t) ->
                                           let uu____12656 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12663 ->
                                                 failwith "Impossible" in
                                           (match uu____12656 with
                                            | (e1,t_norm1) ->
                                                ((let uu___150_12672 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___150_12672.bindings);
                                                    depth =
                                                      (uu___150_12672.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___150_12672.warn);
                                                    cache =
                                                      (uu___150_12672.cache);
                                                    nolabels =
                                                      (uu___150_12672.nolabels);
                                                    use_zfuel_name =
                                                      (uu___150_12672.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___150_12672.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___150_12672.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12633 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12682 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12682
                                            then
                                              let uu____12683 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12684 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12685 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12683 uu____12684
                                                uu____12685
                                            else ());
                                           (let uu____12687 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12687 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12709 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12709
                                                  then
                                                    let uu____12710 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12711 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12712 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12713 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12710 uu____12711
                                                      uu____12712 uu____12713
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12717 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12717 with
                                                  | (vars,guards,env'1,binder_decls,uu____12735)
                                                      ->
                                                      let decl_g =
                                                        let uu____12743 =
                                                          let uu____12749 =
                                                            let uu____12751 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12751 in
                                                          (g, uu____12749,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12743 in
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
                                                        let uu____12766 =
                                                          let uu____12770 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12770) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12766 in
                                                      let gsapp =
                                                        let uu____12776 =
                                                          let uu____12780 =
                                                            let uu____12782 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12782 ::
                                                              vars_tm in
                                                          (g, uu____12780) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12776 in
                                                      let gmax =
                                                        let uu____12786 =
                                                          let uu____12790 =
                                                            let uu____12792 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12792 ::
                                                              vars_tm in
                                                          (g, uu____12790) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12786 in
                                                      let body1 =
                                                        let uu____12796 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12796
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12798 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12798 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12809
                                                               =
                                                               let uu____12813
                                                                 =
                                                                 let uu____12814
                                                                   =
                                                                   let uu____12822
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
                                                                    uu____12822) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12814 in
                                                               let uu____12833
                                                                 =
                                                                 let uu____12835
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12835 in
                                                               (uu____12813,
                                                                 uu____12833,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12809 in
                                                           let eqn_f =
                                                             let uu____12838
                                                               =
                                                               let uu____12842
                                                                 =
                                                                 let uu____12843
                                                                   =
                                                                   let uu____12849
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12849) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12843 in
                                                               (uu____12842,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12838 in
                                                           let eqn_g' =
                                                             let uu____12857
                                                               =
                                                               let uu____12861
                                                                 =
                                                                 let uu____12862
                                                                   =
                                                                   let uu____12868
                                                                    =
                                                                    let uu____12869
                                                                    =
                                                                    let uu____12872
                                                                    =
                                                                    let uu____12873
                                                                    =
                                                                    let uu____12877
                                                                    =
                                                                    let uu____12879
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12879
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12877) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12873 in
                                                                    (gsapp,
                                                                    uu____12872) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12869 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12868) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12862 in
                                                               (uu____12861,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12857 in
                                                           let uu____12891 =
                                                             let uu____12896
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12896
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12913)
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
                                                                    let uu____12928
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12928
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12931
                                                                    =
                                                                    let uu____12935
                                                                    =
                                                                    let uu____12936
                                                                    =
                                                                    let uu____12942
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12942) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12936 in
                                                                    (uu____12935,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12931 in
                                                                 let uu____12953
                                                                   =
                                                                   let uu____12957
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12957
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12965
                                                                    =
                                                                    let uu____12967
                                                                    =
                                                                    let uu____12968
                                                                    =
                                                                    let uu____12972
                                                                    =
                                                                    let uu____12973
                                                                    =
                                                                    let uu____12979
                                                                    =
                                                                    let uu____12980
                                                                    =
                                                                    let uu____12983
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12983,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12980 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12979) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12973 in
                                                                    (uu____12972,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12968 in
                                                                    [uu____12967] in
                                                                    (d3,
                                                                    uu____12965) in
                                                                 (match uu____12953
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12891
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
                               let uu____13018 =
                                 let uu____13025 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____13061  ->
                                      fun uu____13062  ->
                                        match (uu____13061, uu____13062) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____13148 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____13148 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____13025 in
                               (match uu____13018 with
                                | (decls2,eqns,env01) ->
                                    let uu____13188 =
                                      let isDeclFun uu___116_13196 =
                                        match uu___116_13196 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____13197 -> true
                                        | uu____13203 -> false in
                                      let uu____13204 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____13204
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____13188 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____13231 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____13231
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
        let uu____13264 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13264 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____13267 = encode_sigelt' env se in
      match uu____13267 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13277 =
                  let uu____13278 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13278 in
                [uu____13277]
            | uu____13279 ->
                let uu____13280 =
                  let uu____13282 =
                    let uu____13283 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13283 in
                  uu____13282 :: g in
                let uu____13284 =
                  let uu____13286 =
                    let uu____13287 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13287 in
                  [uu____13286] in
                FStar_List.append uu____13280 uu____13284 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____13297 =
          let uu____13298 = FStar_Syntax_Subst.compress t in
          uu____13298.FStar_Syntax_Syntax.n in
        match uu____13297 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____13302)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____13305 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13308 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13311 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13313 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13315 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13323 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13326 =
            let uu____13327 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13327 Prims.op_Negation in
          if uu____13326
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13347 ->
                   let uu____13348 =
                     let uu____13351 =
                       let uu____13352 =
                         let uu____13367 =
                           FStar_All.pipe_left (fun _0_47  -> Some _0_47)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13367) in
                       FStar_Syntax_Syntax.Tm_abs uu____13352 in
                     FStar_Syntax_Syntax.mk uu____13351 in
                   uu____13348 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13420 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13420 with
               | (aname,atok,env2) ->
                   let uu____13430 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13430 with
                    | (formals,uu____13440) ->
                        let uu____13447 =
                          let uu____13450 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13450 env2 in
                        (match uu____13447 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13458 =
                                 let uu____13459 =
                                   let uu____13465 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13473  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13465,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13459 in
                               [uu____13458;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13480 =
                               let aux uu____13509 uu____13510 =
                                 match (uu____13509, uu____13510) with
                                 | ((bv,uu____13537),(env3,acc_sorts,acc)) ->
                                     let uu____13558 = gen_term_var env3 bv in
                                     (match uu____13558 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13480 with
                              | (uu____13596,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13610 =
                                      let uu____13614 =
                                        let uu____13615 =
                                          let uu____13621 =
                                            let uu____13622 =
                                              let uu____13625 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13625) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13622 in
                                          ([[app]], xs_sorts, uu____13621) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13615 in
                                      (uu____13614, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13610 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13637 =
                                      let uu____13641 =
                                        let uu____13642 =
                                          let uu____13648 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13648) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13642 in
                                      (uu____13641,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13637 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13658 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13658 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13674,uu____13675)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13676 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13676 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13687,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13692 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___117_13694  ->
                      match uu___117_13694 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13695 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13698 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13699 -> false)) in
            Prims.op_Negation uu____13692 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13705 = encode_top_level_val env fv t quals in
             match uu____13705 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13717 =
                   let uu____13719 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13719 in
                 (uu____13717, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13724 = encode_formula f env in
          (match uu____13724 with
           | (f1,decls) ->
               let g =
                 let uu____13733 =
                   let uu____13734 =
                     let uu____13738 =
                       let uu____13740 =
                         let uu____13741 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13741 in
                       Some uu____13740 in
                     let uu____13742 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13738, uu____13742) in
                   FStar_SMTEncoding_Util.mkAssume uu____13734 in
                 [uu____13733] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13746,attrs) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right attrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let uu____13754 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13761 =
                       let uu____13766 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13766.FStar_Syntax_Syntax.fv_name in
                     uu____13761.FStar_Syntax_Syntax.v in
                   let uu____13770 =
                     let uu____13771 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13771 in
                   if uu____13770
                   then
                     let val_decl =
                       let uu___151_13786 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___151_13786.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___151_13786.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13790 = encode_sigelt' env1 val_decl in
                     match uu____13790 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____13754 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13807,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13809;
                          FStar_Syntax_Syntax.lbtyp = uu____13810;
                          FStar_Syntax_Syntax.lbeff = uu____13811;
                          FStar_Syntax_Syntax.lbdef = uu____13812;_}::[]),uu____13813,uu____13814)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13828 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13828 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13851 =
                   let uu____13853 =
                     let uu____13854 =
                       let uu____13858 =
                         let uu____13859 =
                           let uu____13865 =
                             let uu____13866 =
                               let uu____13869 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13869) in
                             FStar_SMTEncoding_Util.mkEq uu____13866 in
                           ([[b2t_x]], [xx], uu____13865) in
                         FStar_SMTEncoding_Util.mkForall uu____13859 in
                       (uu____13858, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13854 in
                   [uu____13853] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13851 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13886,uu____13887,uu____13888)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___118_13894  ->
                  match uu___118_13894 with
                  | FStar_Syntax_Syntax.Discriminator uu____13895 -> true
                  | uu____13896 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13898,lids,uu____13900) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13907 =
                     let uu____13908 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13908.FStar_Ident.idText in
                   uu____13907 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___119_13910  ->
                     match uu___119_13910 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13911 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13914,uu____13915)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___120_13925  ->
                  match uu___120_13925 with
                  | FStar_Syntax_Syntax.Projector uu____13926 -> true
                  | uu____13929 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13936 = try_lookup_free_var env l in
          (match uu____13936 with
           | Some uu____13940 -> ([], env)
           | None  ->
               let se1 =
                 let uu___152_13943 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___152_13943.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___152_13943.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13949,uu____13950) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13962) ->
          let uu____13967 = encode_sigelts env ses in
          (match uu____13967 with
           | (g,env1) ->
               let uu____13977 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___121_13987  ->
                         match uu___121_13987 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13988;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13989;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13990;_}
                             -> false
                         | uu____13992 -> true)) in
               (match uu____13977 with
                | (g',inversions) ->
                    let uu____14001 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___122_14011  ->
                              match uu___122_14011 with
                              | FStar_SMTEncoding_Term.DeclFun uu____14012 ->
                                  true
                              | uu____14018 -> false)) in
                    (match uu____14001 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____14029,tps,k,uu____14032,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___123_14042  ->
                    match uu___123_14042 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____14043 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____14050 = c in
              match uu____14050 with
              | (name,args,uu____14054,uu____14055,uu____14056) ->
                  let uu____14059 =
                    let uu____14060 =
                      let uu____14066 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____14073  ->
                                match uu____14073 with
                                | (uu____14077,sort,uu____14079) -> sort)) in
                      (name, uu____14066, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____14060 in
                  [uu____14059]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____14097 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____14100 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____14100 FStar_Option.isNone)) in
            if uu____14097
            then []
            else
              (let uu____14117 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____14117 with
               | (xxsym,xx) ->
                   let uu____14123 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____14134  ->
                             fun l  ->
                               match uu____14134 with
                               | (out,decls) ->
                                   let uu____14146 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____14146 with
                                    | (uu____14152,data_t) ->
                                        let uu____14154 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____14154 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____14183 =
                                                 let uu____14184 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____14184.FStar_Syntax_Syntax.n in
                                               match uu____14183 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____14192,indices) ->
                                                   indices
                                               | uu____14208 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____14220  ->
                                                         match uu____14220
                                                         with
                                                         | (x,uu____14224) ->
                                                             let uu____14225
                                                               =
                                                               let uu____14226
                                                                 =
                                                                 let uu____14230
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____14230,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14226 in
                                                             push_term_var
                                                               env1 x
                                                               uu____14225)
                                                    env) in
                                             let uu____14232 =
                                               encode_args indices env1 in
                                             (match uu____14232 with
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
                                                      let uu____14256 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14264
                                                                 =
                                                                 let uu____14267
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____14267,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14264)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____14256
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____14269 =
                                                      let uu____14270 =
                                                        let uu____14273 =
                                                          let uu____14274 =
                                                            let uu____14277 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____14277,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14274 in
                                                        (out, uu____14273) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14270 in
                                                    (uu____14269,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____14123 with
                    | (data_ax,decls) ->
                        let uu____14285 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14285 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14299 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14299 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14302 =
                                 let uu____14306 =
                                   let uu____14307 =
                                     let uu____14313 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14321 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14313,
                                       uu____14321) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14307 in
                                 let uu____14329 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14306, (Some "inversion axiom"),
                                   uu____14329) in
                               FStar_SMTEncoding_Util.mkAssume uu____14302 in
                             let pattern_guarded_inversion =
                               let uu____14333 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14333
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14344 =
                                   let uu____14345 =
                                     let uu____14349 =
                                       let uu____14350 =
                                         let uu____14356 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14364 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14356, uu____14364) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14350 in
                                     let uu____14372 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14349, (Some "inversion axiom"),
                                       uu____14372) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14345 in
                                 [uu____14344]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14375 =
            let uu____14383 =
              let uu____14384 = FStar_Syntax_Subst.compress k in
              uu____14384.FStar_Syntax_Syntax.n in
            match uu____14383 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14413 -> (tps, k) in
          (match uu____14375 with
           | (formals,res) ->
               let uu____14428 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14428 with
                | (formals1,res1) ->
                    let uu____14435 = encode_binders None formals1 env in
                    (match uu____14435 with
                     | (vars,guards,env',binder_decls,uu____14450) ->
                         let uu____14457 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14457 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14470 =
                                  let uu____14474 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14474) in
                                FStar_SMTEncoding_Util.mkApp uu____14470 in
                              let uu____14479 =
                                let tname_decl =
                                  let uu____14485 =
                                    let uu____14486 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14501  ->
                                              match uu____14501 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14509 = varops.next_id () in
                                    (tname, uu____14486,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14509, false) in
                                  constructor_or_logic_type_decl uu____14485 in
                                let uu____14514 =
                                  match vars with
                                  | [] ->
                                      let uu____14521 =
                                        let uu____14522 =
                                          let uu____14524 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_48  -> Some _0_48)
                                            uu____14524 in
                                        push_free_var env1 t tname
                                          uu____14522 in
                                      ([], uu____14521)
                                  | uu____14528 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14534 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14534 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14543 =
                                          let uu____14547 =
                                            let uu____14548 =
                                              let uu____14556 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14556) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14548 in
                                          (uu____14547,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14543 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14514 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14479 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14579 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14579 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14596 =
                                               let uu____14597 =
                                                 let uu____14601 =
                                                   let uu____14602 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14602 in
                                                 (uu____14601,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14597 in
                                             [uu____14596]
                                           else [] in
                                         let uu____14605 =
                                           let uu____14607 =
                                             let uu____14609 =
                                               let uu____14610 =
                                                 let uu____14614 =
                                                   let uu____14615 =
                                                     let uu____14621 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14621) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14615 in
                                                 (uu____14614, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14610 in
                                             [uu____14609] in
                                           FStar_List.append karr uu____14607 in
                                         FStar_List.append decls1 uu____14605 in
                                   let aux =
                                     let uu____14630 =
                                       let uu____14632 =
                                         inversion_axioms tapp vars in
                                       let uu____14634 =
                                         let uu____14636 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14636] in
                                       FStar_List.append uu____14632
                                         uu____14634 in
                                     FStar_List.append kindingAx uu____14630 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14641,uu____14642,uu____14643,uu____14644,uu____14645)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14650,t,uu____14652,n_tps,uu____14654) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14659 = new_term_constant_and_tok_from_lid env d in
          (match uu____14659 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14670 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14670 with
                | (formals,t_res) ->
                    let uu____14692 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14692 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14701 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14701 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14739 =
                                            mk_term_projector_name d x in
                                          (uu____14739,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14741 =
                                  let uu____14751 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14751, true) in
                                FStar_All.pipe_right uu____14741
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
                              let uu____14773 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14773 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14781::uu____14782 ->
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
                                         let uu____14807 =
                                           let uu____14813 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14813) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14807
                                     | uu____14826 -> tok_typing in
                                   let uu____14831 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14831 with
                                    | (vars',guards',env'',decls_formals,uu____14846)
                                        ->
                                        let uu____14853 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14853 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14872 ->
                                                   let uu____14876 =
                                                     let uu____14877 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14877 in
                                                   [uu____14876] in
                                             let encode_elim uu____14884 =
                                               let uu____14885 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14885 with
                                               | (head1,args) ->
                                                   let uu____14914 =
                                                     let uu____14915 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14915.FStar_Syntax_Syntax.n in
                                                   (match uu____14914 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____14922;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14923;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14924;_},uu____14925)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14935 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14935
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
                                                                 | uu____14961
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14969
                                                                    =
                                                                    let uu____14970
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14970 in
                                                                    if
                                                                    uu____14969
                                                                    then
                                                                    let uu____14977
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14977]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14979
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14992
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14992
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15014
                                                                    =
                                                                    let uu____15018
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15018 in
                                                                    (match uu____15014
                                                                    with
                                                                    | 
                                                                    (uu____15025,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15031
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15031
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15033
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15033
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
                                                             (match uu____14979
                                                              with
                                                              | (uu____15041,arg_vars,elim_eqns_or_guards,uu____15044)
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
                                                                    let uu____15063
                                                                    =
                                                                    let uu____15067
                                                                    =
                                                                    let uu____15068
                                                                    =
                                                                    let uu____15074
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15080
                                                                    =
                                                                    let uu____15081
                                                                    =
                                                                    let uu____15084
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15084) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15081 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15074,
                                                                    uu____15080) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15068 in
                                                                    (uu____15067,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15063 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15097
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15097,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15099
                                                                    =
                                                                    let uu____15103
                                                                    =
                                                                    let uu____15104
                                                                    =
                                                                    let uu____15110
                                                                    =
                                                                    let uu____15113
                                                                    =
                                                                    let uu____15115
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15115] in
                                                                    [uu____15113] in
                                                                    let uu____15118
                                                                    =
                                                                    let uu____15119
                                                                    =
                                                                    let uu____15122
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15123
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15122,
                                                                    uu____15123) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15119 in
                                                                    (uu____15110,
                                                                    [x],
                                                                    uu____15118) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15104 in
                                                                    let uu____15133
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15103,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15133) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15099
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15138
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
                                                                    (let uu____15153
                                                                    =
                                                                    let uu____15154
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15154
                                                                    dapp1 in
                                                                    [uu____15153]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15138
                                                                    FStar_List.flatten in
                                                                    let uu____15158
                                                                    =
                                                                    let uu____15162
                                                                    =
                                                                    let uu____15163
                                                                    =
                                                                    let uu____15169
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15175
                                                                    =
                                                                    let uu____15176
                                                                    =
                                                                    let uu____15179
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15179) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15176 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15169,
                                                                    uu____15175) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15163 in
                                                                    (uu____15162,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15158) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____15195 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15195
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
                                                                 | uu____15221
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15229
                                                                    =
                                                                    let uu____15230
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15230 in
                                                                    if
                                                                    uu____15229
                                                                    then
                                                                    let uu____15237
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15237]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15239
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15252
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15252
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15274
                                                                    =
                                                                    let uu____15278
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15278 in
                                                                    (match uu____15274
                                                                    with
                                                                    | 
                                                                    (uu____15285,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15291
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15291
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15293
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15293
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
                                                             (match uu____15239
                                                              with
                                                              | (uu____15301,arg_vars,elim_eqns_or_guards,uu____15304)
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
                                                                    let uu____15323
                                                                    =
                                                                    let uu____15327
                                                                    =
                                                                    let uu____15328
                                                                    =
                                                                    let uu____15334
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15340
                                                                    =
                                                                    let uu____15341
                                                                    =
                                                                    let uu____15344
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15344) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15341 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15334,
                                                                    uu____15340) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15328 in
                                                                    (uu____15327,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15323 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15357
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15357,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15359
                                                                    =
                                                                    let uu____15363
                                                                    =
                                                                    let uu____15364
                                                                    =
                                                                    let uu____15370
                                                                    =
                                                                    let uu____15373
                                                                    =
                                                                    let uu____15375
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15375] in
                                                                    [uu____15373] in
                                                                    let uu____15378
                                                                    =
                                                                    let uu____15379
                                                                    =
                                                                    let uu____15382
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15383
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15382,
                                                                    uu____15383) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15379 in
                                                                    (uu____15370,
                                                                    [x],
                                                                    uu____15378) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15364 in
                                                                    let uu____15393
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15363,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15393) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15359
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15398
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
                                                                    (let uu____15413
                                                                    =
                                                                    let uu____15414
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15414
                                                                    dapp1 in
                                                                    [uu____15413]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15398
                                                                    FStar_List.flatten in
                                                                    let uu____15418
                                                                    =
                                                                    let uu____15422
                                                                    =
                                                                    let uu____15423
                                                                    =
                                                                    let uu____15429
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15435
                                                                    =
                                                                    let uu____15436
                                                                    =
                                                                    let uu____15439
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15439) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15436 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15429,
                                                                    uu____15435) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15423 in
                                                                    (uu____15422,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15418) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15449 ->
                                                        ((let uu____15451 =
                                                            let uu____15452 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15453 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15452
                                                              uu____15453 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15451);
                                                         ([], []))) in
                                             let uu____15456 = encode_elim () in
                                             (match uu____15456 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15468 =
                                                      let uu____15470 =
                                                        let uu____15472 =
                                                          let uu____15474 =
                                                            let uu____15476 =
                                                              let uu____15477
                                                                =
                                                                let uu____15483
                                                                  =
                                                                  let uu____15485
                                                                    =
                                                                    let uu____15486
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15486 in
                                                                  Some
                                                                    uu____15485 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15483) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15477 in
                                                            [uu____15476] in
                                                          let uu____15489 =
                                                            let uu____15491 =
                                                              let uu____15493
                                                                =
                                                                let uu____15495
                                                                  =
                                                                  let uu____15497
                                                                    =
                                                                    let uu____15499
                                                                    =
                                                                    let uu____15501
                                                                    =
                                                                    let uu____15502
                                                                    =
                                                                    let uu____15506
                                                                    =
                                                                    let uu____15507
                                                                    =
                                                                    let uu____15513
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15513) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15507 in
                                                                    (uu____15506,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15502 in
                                                                    let uu____15520
                                                                    =
                                                                    let uu____15522
                                                                    =
                                                                    let uu____15523
                                                                    =
                                                                    let uu____15527
                                                                    =
                                                                    let uu____15528
                                                                    =
                                                                    let uu____15534
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____15540
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15534,
                                                                    uu____15540) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15528 in
                                                                    (uu____15527,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15523 in
                                                                    [uu____15522] in
                                                                    uu____15501
                                                                    ::
                                                                    uu____15520 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15499 in
                                                                  FStar_List.append
                                                                    uu____15497
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15495 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15493 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15491 in
                                                          FStar_List.append
                                                            uu____15474
                                                            uu____15489 in
                                                        FStar_List.append
                                                          decls3 uu____15472 in
                                                      FStar_List.append
                                                        decls2 uu____15470 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15468 in
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
           (fun uu____15561  ->
              fun se  ->
                match uu____15561 with
                | (g,env1) ->
                    let uu____15573 = encode_sigelt env1 se in
                    (match uu____15573 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15611 =
        match uu____15611 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15629 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____15634 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15634
                   then
                     let uu____15635 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15636 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15637 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15635 uu____15636 uu____15637
                   else ());
                  (let uu____15639 = encode_term t1 env1 in
                   match uu____15639 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15649 =
                         let uu____15653 =
                           let uu____15654 =
                             let uu____15655 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15655
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15654 in
                         new_term_constant_from_string env1 x uu____15653 in
                       (match uu____15649 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15666 = FStar_Options.log_queries () in
                              if uu____15666
                              then
                                let uu____15668 =
                                  let uu____15669 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15670 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15671 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15669 uu____15670 uu____15671 in
                                Some uu____15668
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15682,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15691 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15691 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15704,se,uu____15706) ->
                 let uu____15709 = encode_sigelt env1 se in
                 (match uu____15709 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15719,se) ->
                 let uu____15723 = encode_sigelt env1 se in
                 (match uu____15723 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15733 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15733 with | (uu____15745,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15793  ->
            match uu____15793 with
            | (l,uu____15800,uu____15801) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15822  ->
            match uu____15822 with
            | (l,uu____15830,uu____15831) ->
                let uu____15836 =
                  FStar_All.pipe_left
                    (fun _0_49  -> FStar_SMTEncoding_Term.Echo _0_49) (
                    fst l) in
                let uu____15837 =
                  let uu____15839 =
                    let uu____15840 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15840 in
                  [uu____15839] in
                uu____15836 :: uu____15837)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15852 =
      let uu____15854 =
        let uu____15855 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15857 =
          let uu____15858 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15858 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15855;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15857
        } in
      [uu____15854] in
    FStar_ST.write last_env uu____15852
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15870 = FStar_ST.read last_env in
      match uu____15870 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15876 ->
          let uu___153_15878 = e in
          let uu____15879 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___153_15878.bindings);
            depth = (uu___153_15878.depth);
            tcenv;
            warn = (uu___153_15878.warn);
            cache = (uu___153_15878.cache);
            nolabels = (uu___153_15878.nolabels);
            use_zfuel_name = (uu___153_15878.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___153_15878.encode_non_total_function_typ);
            current_module_name = uu____15879
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15884 = FStar_ST.read last_env in
    match uu____15884 with
    | [] -> failwith "Empty env stack"
    | uu____15889::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15898  ->
    let uu____15899 = FStar_ST.read last_env in
    match uu____15899 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___154_15910 = hd1 in
          {
            bindings = (uu___154_15910.bindings);
            depth = (uu___154_15910.depth);
            tcenv = (uu___154_15910.tcenv);
            warn = (uu___154_15910.warn);
            cache = refs;
            nolabels = (uu___154_15910.nolabels);
            use_zfuel_name = (uu___154_15910.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15910.encode_non_total_function_typ);
            current_module_name = (uu___154_15910.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15917  ->
    let uu____15918 = FStar_ST.read last_env in
    match uu____15918 with
    | [] -> failwith "Popping an empty stack"
    | uu____15923::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15932  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15936  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15940  ->
    let uu____15941 = FStar_ST.read last_env in
    match uu____15941 with
    | hd1::uu____15947::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15953 -> failwith "Impossible"
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
        | (uu____16012::uu____16013,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___155_16017 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___155_16017.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___155_16017.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___155_16017.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____16018 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____16031 =
        let uu____16033 =
          let uu____16034 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____16034 in
        let uu____16035 = open_fact_db_tags env in uu____16033 :: uu____16035 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____16031
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
      let uu____16052 = encode_sigelt env se in
      match uu____16052 with
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
        let uu____16079 = FStar_Options.log_queries () in
        if uu____16079
        then
          let uu____16081 =
            let uu____16082 =
              let uu____16083 =
                let uu____16084 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____16084 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____16083 in
            FStar_SMTEncoding_Term.Caption uu____16082 in
          uu____16081 :: decls
        else decls in
      let env =
        let uu____16091 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16091 tcenv in
      let uu____16092 = encode_top_level_facts env se in
      match uu____16092 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____16101 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____16101))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____16114 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____16114
       then
         let uu____16115 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____16115
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____16138  ->
                 fun se  ->
                   match uu____16138 with
                   | (g,env2) ->
                       let uu____16150 = encode_top_level_facts env2 se in
                       (match uu____16150 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____16163 =
         encode_signature
           (let uu___156_16167 = env in
            {
              bindings = (uu___156_16167.bindings);
              depth = (uu___156_16167.depth);
              tcenv = (uu___156_16167.tcenv);
              warn = false;
              cache = (uu___156_16167.cache);
              nolabels = (uu___156_16167.nolabels);
              use_zfuel_name = (uu___156_16167.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_16167.encode_non_total_function_typ);
              current_module_name = (uu___156_16167.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____16163 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____16179 = FStar_Options.log_queries () in
             if uu____16179
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___157_16184 = env1 in
               {
                 bindings = (uu___157_16184.bindings);
                 depth = (uu___157_16184.depth);
                 tcenv = (uu___157_16184.tcenv);
                 warn = true;
                 cache = (uu___157_16184.cache);
                 nolabels = (uu___157_16184.nolabels);
                 use_zfuel_name = (uu___157_16184.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___157_16184.encode_non_total_function_typ);
                 current_module_name = (uu___157_16184.current_module_name)
               });
            (let uu____16186 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____16186
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
        (let uu____16224 =
           let uu____16225 = FStar_TypeChecker_Env.current_module tcenv in
           uu____16225.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16224);
        (let env =
           let uu____16227 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____16227 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____16234 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16255 = aux rest in
                 (match uu____16255 with
                  | (out,rest1) ->
                      let t =
                        let uu____16273 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____16273 with
                        | Some uu____16277 ->
                            let uu____16278 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16278
                              x.FStar_Syntax_Syntax.sort
                        | uu____16279 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____16282 =
                        let uu____16284 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___158_16285 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_16285.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_16285.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16284 :: out in
                      (uu____16282, rest1))
             | uu____16288 -> ([], bindings1) in
           let uu____16292 = aux bindings in
           match uu____16292 with
           | (closing,bindings1) ->
               let uu____16306 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16306, bindings1) in
         match uu____16234 with
         | (q1,bindings1) ->
             let uu____16319 =
               let uu____16322 =
                 FStar_List.filter
                   (fun uu___124_16324  ->
                      match uu___124_16324 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16325 ->
                          false
                      | uu____16329 -> true) bindings1 in
               encode_env_bindings env uu____16322 in
             (match uu____16319 with
              | (env_decls,env1) ->
                  ((let uu____16340 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16340
                    then
                      let uu____16341 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16341
                    else ());
                   (let uu____16343 = encode_formula q1 env1 in
                    match uu____16343 with
                    | (phi,qdecls) ->
                        let uu____16355 =
                          let uu____16358 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16358 phi in
                        (match uu____16355 with
                         | (labels,phi1) ->
                             let uu____16368 = encode_labels labels in
                             (match uu____16368 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____16389 =
                                      let uu____16393 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16394 =
                                        varops.mk_unique "@query" in
                                      (uu____16393, (Some "query"),
                                        uu____16394) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16389 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16409 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16409 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16411 = encode_formula q env in
       match uu____16411 with
       | (f,uu____16415) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16417) -> true
             | uu____16420 -> false)))