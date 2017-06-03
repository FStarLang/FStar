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
             | uu____195 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____202 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____202
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____209 =
        let uu____212 = mk_term_projector_name lid a in
        (uu____212,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____209
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____219 =
        let uu____222 = mk_term_projector_name_by_pos lid i in
        (uu____222,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____219
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
  let new_scope uu____412 =
    let uu____413 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____415 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____413, uu____415) in
  let scopes =
    let uu____426 = let uu____432 = new_scope () in [uu____432] in
    FStar_Util.mk_ref uu____426 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____457 =
        let uu____459 = FStar_ST.read scopes in
        FStar_Util.find_map uu____459
          (fun uu____476  ->
             match uu____476 with
             | (names1,uu____483) -> FStar_Util.smap_try_find names1 y1) in
      match uu____457 with
      | None  -> y1
      | Some uu____488 ->
          (FStar_Util.incr ctr;
           (let uu____493 =
              let uu____494 =
                let uu____495 = FStar_ST.read ctr in
                Prims.string_of_int uu____495 in
              Prims.strcat "__" uu____494 in
            Prims.strcat y1 uu____493)) in
    let top_scope =
      let uu____500 =
        let uu____505 = FStar_ST.read scopes in FStar_List.hd uu____505 in
      FStar_All.pipe_left FStar_Pervasives.fst uu____500 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____544 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____555 =
      let uu____556 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____556 in
    FStar_Util.format2 "%s_%s" pfx uu____555 in
  let string_const s =
    let uu____561 =
      let uu____563 = FStar_ST.read scopes in
      FStar_Util.find_map uu____563
        (fun uu____580  ->
           match uu____580 with
           | (uu____586,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____561 with
    | Some f -> f
    | None  ->
        let id = next_id1 () in
        let f =
          let uu____595 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____595 in
        let top_scope =
          let uu____598 =
            let uu____603 = FStar_ST.read scopes in FStar_List.hd uu____603 in
          FStar_All.pipe_left FStar_Pervasives.snd uu____598 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____631 =
    let uu____632 =
      let uu____638 = new_scope () in
      let uu____643 = FStar_ST.read scopes in uu____638 :: uu____643 in
    FStar_ST.write scopes uu____632 in
  let pop1 uu____670 =
    let uu____671 =
      let uu____677 = FStar_ST.read scopes in FStar_List.tl uu____677 in
    FStar_ST.write scopes uu____671 in
  let mark1 uu____704 = push1 () in
  let reset_mark1 uu____708 = pop1 () in
  let commit_mark1 uu____712 =
    let uu____713 = FStar_ST.read scopes in
    match uu____713 with
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
    | uu____773 -> failwith "Impossible" in
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
    let uu___128_782 = x in
    let uu____783 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____783;
      FStar_Syntax_Syntax.index = (uu___128_782.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___128_782.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term option* FStar_SMTEncoding_Term.term option)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____804 -> false
let __proj__Binding_var__item___0:
  binding -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____828 -> false
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
         (fun uu___103_1003  ->
            match uu___103_1003 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1006 -> [])) in
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
    let uu____1014 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___104_1018  ->
              match uu___104_1018 with
              | Binding_var (x,uu____1020) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1022,uu____1023,uu____1024) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1014 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string option =
  fun env  ->
    fun t  ->
      let uu____1057 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1057
      then
        let uu____1059 = FStar_Syntax_Print.term_to_string t in
        Some uu____1059
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1070 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1070)
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
        (let uu___129_1082 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___129_1082.tcenv);
           warn = (uu___129_1082.warn);
           cache = (uu___129_1082.cache);
           nolabels = (uu___129_1082.nolabels);
           use_zfuel_name = (uu___129_1082.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___129_1082.encode_non_total_function_typ);
           current_module_name = (uu___129_1082.current_module_name)
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
        (let uu___130_1095 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___130_1095.depth);
           tcenv = (uu___130_1095.tcenv);
           warn = (uu___130_1095.warn);
           cache = (uu___130_1095.cache);
           nolabels = (uu___130_1095.nolabels);
           use_zfuel_name = (uu___130_1095.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___130_1095.encode_non_total_function_typ);
           current_module_name = (uu___130_1095.current_module_name)
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
          (let uu___131_1111 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___131_1111.depth);
             tcenv = (uu___131_1111.tcenv);
             warn = (uu___131_1111.warn);
             cache = (uu___131_1111.cache);
             nolabels = (uu___131_1111.nolabels);
             use_zfuel_name = (uu___131_1111.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___131_1111.encode_non_total_function_typ);
             current_module_name = (uu___131_1111.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___132_1121 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___132_1121.depth);
          tcenv = (uu___132_1121.tcenv);
          warn = (uu___132_1121.warn);
          cache = (uu___132_1121.cache);
          nolabels = (uu___132_1121.nolabels);
          use_zfuel_name = (uu___132_1121.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___132_1121.encode_non_total_function_typ);
          current_module_name = (uu___132_1121.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___105_1137  ->
             match uu___105_1137 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1145 -> None) in
      let uu____1148 = aux a in
      match uu____1148 with
      | None  ->
          let a2 = unmangle a in
          let uu____1155 = aux a2 in
          (match uu____1155 with
           | None  ->
               let uu____1161 =
                 let uu____1162 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1163 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1162 uu____1163 in
               failwith uu____1161
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1183 =
        let uu___133_1184 = env in
        let uu____1185 =
          let uu____1187 =
            let uu____1188 =
              let uu____1195 =
                let uu____1197 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1197 in
              (x, fname, uu____1195, None) in
            Binding_fvar uu____1188 in
          uu____1187 :: (env.bindings) in
        {
          bindings = uu____1185;
          depth = (uu___133_1184.depth);
          tcenv = (uu___133_1184.tcenv);
          warn = (uu___133_1184.warn);
          cache = (uu___133_1184.cache);
          nolabels = (uu___133_1184.nolabels);
          use_zfuel_name = (uu___133_1184.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___133_1184.encode_non_total_function_typ);
          current_module_name = (uu___133_1184.current_module_name)
        } in
      (fname, ftok, uu____1183)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option) option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___106_1219  ->
           match uu___106_1219 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1241 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1253 =
        lookup_binding env
          (fun uu___107_1255  ->
             match uu___107_1255 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1265 -> None) in
      FStar_All.pipe_right uu____1253 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option)
  =
  fun env  ->
    fun a  ->
      let uu____1278 = try_lookup_lid env a in
      match uu____1278 with
      | None  ->
          let uu____1295 =
            let uu____1296 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1296 in
          failwith uu____1295
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
          let uu___134_1327 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___134_1327.depth);
            tcenv = (uu___134_1327.tcenv);
            warn = (uu___134_1327.warn);
            cache = (uu___134_1327.cache);
            nolabels = (uu___134_1327.nolabels);
            use_zfuel_name = (uu___134_1327.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___134_1327.encode_non_total_function_typ);
            current_module_name = (uu___134_1327.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1339 = lookup_lid env x in
        match uu____1339 with
        | (t1,t2,uu____1347) ->
            let t3 =
              let uu____1353 =
                let uu____1357 =
                  let uu____1359 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1359] in
                (f, uu____1357) in
              FStar_SMTEncoding_Util.mkApp uu____1353 in
            let uu___135_1362 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___135_1362.depth);
              tcenv = (uu___135_1362.tcenv);
              warn = (uu___135_1362.warn);
              cache = (uu___135_1362.cache);
              nolabels = (uu___135_1362.nolabels);
              use_zfuel_name = (uu___135_1362.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___135_1362.encode_non_total_function_typ);
              current_module_name = (uu___135_1362.current_module_name)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term option =
  fun env  ->
    fun l  ->
      let uu____1372 = try_lookup_lid env l in
      match uu____1372 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1399 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1404,fuel::[]) ->
                         let uu____1407 =
                           let uu____1408 =
                             let uu____1409 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1409
                               FStar_Pervasives.fst in
                           FStar_Util.starts_with uu____1408 "fuel" in
                         if uu____1407
                         then
                           let uu____1411 =
                             let uu____1412 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1412
                               fuel in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1411
                         else Some t
                     | uu____1415 -> Some t)
                | uu____1416 -> None))
let lookup_free_var env a =
  let uu____1434 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1434 with
  | Some t -> t
  | None  ->
      let uu____1437 =
        let uu____1438 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1438 in
      failwith uu____1437
let lookup_free_var_name env a =
  let uu____1455 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1455 with | (x,uu____1462,uu____1463) -> x
let lookup_free_var_sym env a =
  let uu____1487 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1487 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1508;
             FStar_SMTEncoding_Term.rng = uu____1509;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1517 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1531 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name: env_t -> Prims.string -> FStar_SMTEncoding_Term.term option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___108_1540  ->
           match uu___108_1540 with
           | Binding_fvar (uu____1542,nm',tok,uu____1545) when nm = nm' ->
               tok
           | uu____1550 -> None)
let mkForall_fuel' n1 uu____1567 =
  match uu____1567 with
  | (pats,vars,body) ->
      let fallback uu____1583 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1586 = FStar_Options.unthrottle_inductives () in
      if uu____1586
      then fallback ()
      else
        (let uu____1588 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1588 with
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
                       | uu____1607 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1621 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1621
                     | uu____1623 ->
                         let uu____1624 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1624 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1627 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____1653 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____1661 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____1666 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____1667 -> true
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
               (fun uu___109_1779  ->
                  match uu___109_1779 with
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
  fun uu___110_1884  ->
    match uu___110_1884 with
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
                          | uu____1947 -> false) args (FStar_List.rev xs)) in
              if uu____1933 then tok_of_name env f else None
          | (uu____1950,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1953 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1955 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1955)) in
              if uu____1953 then Some t else None
          | uu____1958 -> None in
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
    | uu____2042 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___111_2045  ->
    match uu___111_2045 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2047 =
          let uu____2051 =
            let uu____2053 =
              let uu____2054 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2054 in
            [uu____2053] in
          ("FStar.Char.Char", uu____2051) in
        FStar_SMTEncoding_Util.mkApp uu____2047
    | FStar_Const.Const_int (i,None ) ->
        let uu____2062 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2062
    | FStar_Const.Const_int (i,Some uu____2064) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2073) ->
        let uu____2076 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2076
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2080 =
          let uu____2081 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2081 in
        failwith uu____2080
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2100 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2108 ->
            let uu____2113 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2113
        | uu____2114 ->
            if norm1
            then let uu____2115 = whnf env t1 in aux false uu____2115
            else
              (let uu____2117 =
                 let uu____2118 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2119 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2118 uu____2119 in
               failwith uu____2117) in
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
    | uu____2140 ->
        let uu____2141 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2141)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2169::uu____2170::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Syntax_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2173::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2175 -> false
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
        (let uu____2313 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2313
         then
           let uu____2314 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2314
         else ());
        (let uu____2316 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2352  ->
                   fun b  ->
                     match uu____2352 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2395 =
                           let x = unmangle (fst b) in
                           let uu____2404 = gen_term_var env1 x in
                           match uu____2404 with
                           | (xxsym,xx,env') ->
                               let uu____2418 =
                                 let uu____2421 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2421 env1 xx in
                               (match uu____2418 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2395 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2316 with
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
          let uu____2509 = encode_term t env in
          match uu____2509 with
          | (t1,decls) ->
              let uu____2516 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2516, decls)
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
          let uu____2524 = encode_term t env in
          match uu____2524 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2533 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2533, decls)
               | Some f ->
                   let uu____2535 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2535, decls))
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
        let uu____2541 = encode_args args_e env in
        match uu____2541 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2553 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____2560 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____2560 in
            let binary arg_tms1 =
              let uu____2569 =
                let uu____2570 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____2570 in
              let uu____2571 =
                let uu____2572 =
                  let uu____2573 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2573 in
                FStar_SMTEncoding_Term.unboxInt uu____2572 in
              (uu____2569, uu____2571) in
            let mk_default uu____2578 =
              let uu____2579 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2579 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____2624 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2624
              then
                let uu____2625 = let uu____2626 = mk_args ts in op uu____2626 in
                FStar_All.pipe_right uu____2625 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____2649 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____2649
              then
                let uu____2650 = binary ts in
                match uu____2650 with
                | (t1,t2) ->
                    let uu____2655 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____2655
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2658 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____2658
                 then
                   let uu____2659 = op (binary ts) in
                   FStar_All.pipe_right uu____2659
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
            let uu____2749 =
              let uu____2755 =
                FStar_List.tryFind
                  (fun uu____2767  ->
                     match uu____2767 with
                     | (l,uu____2774) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____2755 FStar_Util.must in
            (match uu____2749 with
             | (uu____2799,op) ->
                 let uu____2807 = op arg_tms in (uu____2807, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2814 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2814
       then
         let uu____2815 = FStar_Syntax_Print.tag_of_term t in
         let uu____2816 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2817 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2815 uu____2816
           uu____2817
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2821 ->
           let uu____2842 =
             let uu____2843 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2844 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2845 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2846 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2843
               uu____2844 uu____2845 uu____2846 in
           failwith uu____2842
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2849 =
             let uu____2850 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2851 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2852 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2853 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2850
               uu____2851 uu____2852 uu____2853 in
           failwith uu____2849
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2857 =
             let uu____2858 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2858 in
           failwith uu____2857
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2863) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2893) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2902 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2902, [])
       | FStar_Syntax_Syntax.Tm_type uu____2908 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2911) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2917 = encode_const c in (uu____2917, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2932 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2932 with
            | (binders1,res) ->
                let uu____2939 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2939
                then
                  let uu____2942 = encode_binders None binders1 env in
                  (match uu____2942 with
                   | (vars,guards,env',decls,uu____2957) ->
                       let fsym =
                         let uu____2967 = varops.fresh "f" in
                         (uu____2967, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2970 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___136_2974 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___136_2974.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___136_2974.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___136_2974.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___136_2974.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___136_2974.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___136_2974.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___136_2974.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___136_2974.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___136_2974.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___136_2974.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___136_2974.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___136_2974.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___136_2974.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___136_2974.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___136_2974.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___136_2974.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___136_2974.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___136_2974.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___136_2974.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___136_2974.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___136_2974.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___136_2974.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___136_2974.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___136_2974.FStar_TypeChecker_Env.proof_ns)
                            }) res in
                       (match uu____2970 with
                        | (pre_opt,res_t) ->
                            let uu____2981 =
                              encode_term_pred None res_t env' app in
                            (match uu____2981 with
                             | (res_pred,decls') ->
                                 let uu____2988 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2995 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2995, [])
                                   | Some pre ->
                                       let uu____2998 =
                                         encode_formula pre env' in
                                       (match uu____2998 with
                                        | (guard,decls0) ->
                                            let uu____3006 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3006, decls0)) in
                                 (match uu____2988 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3014 =
                                          let uu____3020 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3020) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3014 in
                                      let cvars =
                                        let uu____3030 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3030
                                          (FStar_List.filter
                                             (fun uu____3036  ->
                                                match uu____3036 with
                                                | (x,uu____3040) ->
                                                    x <> (fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3051 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3051 with
                                       | Some cache_entry ->
                                           let uu____3056 =
                                             let uu____3057 =
                                               let uu____3061 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3061) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3057 in
                                           (uu____3056,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____3072 =
                                               let uu____3073 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3073 in
                                             varops.mk_unique uu____3072 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars in
                                           let caption =
                                             let uu____3080 =
                                               FStar_Options.log_queries () in
                                             if uu____3080
                                             then
                                               let uu____3082 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____3082
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3088 =
                                               let uu____3092 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3092) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3088 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3100 =
                                               let uu____3104 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3104, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3100 in
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
                                             let uu____3117 =
                                               let uu____3121 =
                                                 let uu____3122 =
                                                   let uu____3128 =
                                                     let uu____3129 =
                                                       let uu____3132 =
                                                         let uu____3133 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3133 in
                                                       (f_has_t, uu____3132) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3129 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3128) in
                                                 mkForall_fuel uu____3122 in
                                               (uu____3121,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3117 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3146 =
                                               let uu____3150 =
                                                 let uu____3151 =
                                                   let uu____3157 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3157) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3151 in
                                               (uu____3150, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3146 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3171 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3171);
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
                     let uu____3182 =
                       let uu____3186 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3186, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3182 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3195 =
                       let uu____3199 =
                         let uu____3200 =
                           let uu____3206 =
                             let uu____3207 =
                               let uu____3210 =
                                 let uu____3211 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3211 in
                               (f_has_t, uu____3210) in
                             FStar_SMTEncoding_Util.mkImp uu____3207 in
                           ([[f_has_t]], [fsym], uu____3206) in
                         mkForall_fuel uu____3200 in
                       (uu____3199, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3195 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3225 ->
           let uu____3230 =
             let uu____3233 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3233 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3238;
                 FStar_Syntax_Syntax.pos = uu____3239;
                 FStar_Syntax_Syntax.vars = uu____3240;_} ->
                 let uu____3247 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____3247 with
                  | (b,f1) ->
                      let uu____3261 =
                        let uu____3262 = FStar_List.hd b in fst uu____3262 in
                      (uu____3261, f1))
             | uu____3267 -> failwith "impossible" in
           (match uu____3230 with
            | (x,f) ->
                let uu____3274 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3274 with
                 | (base_t,decls) ->
                     let uu____3281 = gen_term_var env x in
                     (match uu____3281 with
                      | (x1,xtm,env') ->
                          let uu____3290 = encode_formula f env' in
                          (match uu____3290 with
                           | (refinement,decls') ->
                               let uu____3297 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3297 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3308 =
                                        let uu____3310 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3314 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3310
                                          uu____3314 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3308 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3330  ->
                                              match uu____3330 with
                                              | (y,uu____3334) ->
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
                                    let uu____3353 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3353 with
                                     | Some cache_entry ->
                                         let uu____3358 =
                                           let uu____3359 =
                                             let uu____3363 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3363) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3359 in
                                         (uu____3358,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3375 =
                                             let uu____3376 =
                                               let uu____3377 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3377 in
                                             Prims.strcat module_name
                                               uu____3376 in
                                           varops.mk_unique uu____3375 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3386 =
                                             let uu____3390 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3390) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3386 in
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
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____3427 =
                                             let uu____3431 =
                                               let uu____3432 =
                                                 let uu____3438 =
                                                   let uu____3439 =
                                                     let uu____3442 =
                                                       let uu____3443 =
                                                         let uu____3449 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____3449) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____3443 in
                                                     (uu____3442, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____3439 in
                                                 ([[valid_t]], cvars1,
                                                   uu____3438) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3432 in
                                             (uu____3431,
                                               (Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3427 in
                                         let t_kinding =
                                           let uu____3469 =
                                             let uu____3473 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3473,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3469 in
                                         let t_interp =
                                           let uu____3483 =
                                             let uu____3487 =
                                               let uu____3488 =
                                                 let uu____3494 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3494) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3488 in
                                             let uu____3506 =
                                               let uu____3508 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3508 in
                                             (uu____3487, uu____3506,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3483 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3513 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3513);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3530 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3530 in
           let uu____3531 = encode_term_pred None k env ttm in
           (match uu____3531 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3539 =
                    let uu____3543 =
                      let uu____3544 =
                        let uu____3545 =
                          let uu____3546 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3546 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3545 in
                      varops.mk_unique uu____3544 in
                    (t_has_k, (Some "Uvar typing"), uu____3543) in
                  FStar_SMTEncoding_Util.mkAssume uu____3539 in
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
                                              (fun uu____3924  ->
                                                 fun uu____3925  ->
                                                   match (uu____3924,
                                                           uu____3925)
                                                   with
                                                   | ((bv,uu____3939),
                                                      (a,uu____3941)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3955 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3955
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3960 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3960 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3970 =
                                                   let uu____3974 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3979 =
                                                     let uu____3980 =
                                                       let uu____3981 =
                                                         let uu____3982 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3982 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3981 in
                                                     varops.mk_unique
                                                       uu____3980 in
                                                   (uu____3974,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3979) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3970 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3999 = lookup_free_var_sym env fv in
                            match uu____3999 with
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
                                   FStar_Syntax_Syntax.tk = uu____4022;
                                   FStar_Syntax_Syntax.pos = uu____4023;
                                   FStar_Syntax_Syntax.vars = uu____4024;_},uu____4025)
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____4036;
                                   FStar_Syntax_Syntax.pos = uu____4037;
                                   FStar_Syntax_Syntax.vars = uu____4038;_},uu____4039)
                                ->
                                let uu____4044 =
                                  let uu____4045 =
                                    let uu____4048 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4048
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4045
                                    FStar_Pervasives.snd in
                                Some uu____4044
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4068 =
                                  let uu____4069 =
                                    let uu____4072 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4072
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4069
                                    FStar_Pervasives.snd in
                                Some uu____4068
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4091,(FStar_Util.Inl t1,uu____4093),uu____4094)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4132,(FStar_Util.Inr c,uu____4134),uu____4135)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4173 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4193 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4193 in
                               let uu____4194 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4194 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4204;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4205;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4206;_},uu____4207)
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
                                     | uu____4239 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4289 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4289 with
            | (bs1,body1,opening) ->
                let fallback uu____4304 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____4309 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4309, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4320 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____4320
                  | FStar_Util.Inr (eff,uu____4322) ->
                      let uu____4328 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____4328 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4373 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___137_4374 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___137_4374.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___137_4374.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___137_4374.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___137_4374.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___137_4374.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___137_4374.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___137_4374.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___137_4374.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___137_4374.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___137_4374.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___137_4374.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___137_4374.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___137_4374.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___137_4374.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___137_4374.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___137_4374.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___137_4374.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___137_4374.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___137_4374.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___137_4374.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___137_4374.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___137_4374.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___137_4374.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___137_4374.FStar_TypeChecker_Env.proof_ns)
                             }) uu____4373 FStar_Syntax_Syntax.U_unknown in
                        let uu____4375 =
                          let uu____4376 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4376 in
                        FStar_Util.Inl uu____4375
                    | FStar_Util.Inr (eff_name,uu____4383) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4414 =
                        let uu____4415 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4415 in
                      FStar_All.pipe_right uu____4414
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4427 =
                        let uu____4428 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4428 FStar_Pervasives.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4436 =
                          let uu____4437 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4437 in
                        FStar_All.pipe_right uu____4436
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4441 =
                             let uu____4442 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4442 in
                           FStar_All.pipe_right uu____4441
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4453 =
                         let uu____4454 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4454 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4453);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4469 =
                       (is_impure lc1) &&
                         (let uu____4470 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4470) in
                     if uu____4469
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4475 = encode_binders None bs1 env in
                        match uu____4475 with
                        | (vars,guards,envbody,decls,uu____4490) ->
                            let uu____4497 =
                              let uu____4505 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4505
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4497 with
                             | (lc2,body2) ->
                                 let uu____4530 = encode_term body2 envbody in
                                 (match uu____4530 with
                                  | (body3,decls') ->
                                      let uu____4537 =
                                        let uu____4542 = codomain_eff lc2 in
                                        match uu____4542 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4554 =
                                              encode_term tfun env in
                                            (match uu____4554 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4537 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4573 =
                                               let uu____4579 =
                                                 let uu____4580 =
                                                   let uu____4583 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4583, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4580 in
                                               ([], vars, uu____4579) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4573 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4591 =
                                                   let uu____4593 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4593 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4591 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4604 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4604 with
                                            | Some cache_entry ->
                                                let uu____4609 =
                                                  let uu____4610 =
                                                    let uu____4614 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4614) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4610 in
                                                (uu____4609,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | None  ->
                                                let uu____4620 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4620 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4627 =
                                                         let uu____4628 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4628 =
                                                           cache_size in
                                                       if uu____4627
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
                                                         let uu____4639 =
                                                           let uu____4640 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4640 in
                                                         varops.mk_unique
                                                           uu____4639 in
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
                                                       let uu____4645 =
                                                         let uu____4649 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4649) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4645 in
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
                                                           let uu____4661 =
                                                             let uu____4662 =
                                                               let uu____4666
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4666,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4662 in
                                                           [uu____4661] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4674 =
                                                         let uu____4678 =
                                                           let uu____4679 =
                                                             let uu____4685 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4685) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4679 in
                                                         (uu____4678,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4674 in
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
                                                     ((let uu____4695 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4695);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4697,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4698;
                          FStar_Syntax_Syntax.lbunivs = uu____4699;
                          FStar_Syntax_Syntax.lbtyp = uu____4700;
                          FStar_Syntax_Syntax.lbeff = uu____4701;
                          FStar_Syntax_Syntax.lbdef = uu____4702;_}::uu____4703),uu____4704)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4722;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4724;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4740 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4753 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4753, [decl_e])))
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
              let uu____4795 = encode_term e1 env in
              match uu____4795 with
              | (ee1,decls1) ->
                  let uu____4802 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4802 with
                   | (xs,e21) ->
                       let uu____4816 = FStar_List.hd xs in
                       (match uu____4816 with
                        | (x1,uu____4824) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4826 = encode_body e21 env' in
                            (match uu____4826 with
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
            let uu____4848 =
              let uu____4852 =
                let uu____4853 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4853 in
              gen_term_var env uu____4852 in
            match uu____4848 with
            | (scrsym,scr',env1) ->
                let uu____4863 = encode_term e env1 in
                (match uu____4863 with
                 | (scr,decls) ->
                     let uu____4870 =
                       let encode_branch b uu____4886 =
                         match uu____4886 with
                         | (else_case,decls1) ->
                             let uu____4897 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4897 with
                              | (p,w,br) ->
                                  let uu____4918 = encode_pat env1 p in
                                  (match uu____4918 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____4938  ->
                                                   match uu____4938 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____4943 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____4958 =
                                               encode_term w1 env2 in
                                             (match uu____4958 with
                                              | (w2,decls2) ->
                                                  let uu____4966 =
                                                    let uu____4967 =
                                                      let uu____4970 =
                                                        let uu____4971 =
                                                          let uu____4974 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____4974) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____4971 in
                                                      (guard, uu____4970) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____4967 in
                                                  (uu____4966, decls2)) in
                                       (match uu____4943 with
                                        | (guard1,decls2) ->
                                            let uu____4982 =
                                              encode_br br env2 in
                                            (match uu____4982 with
                                             | (br1,decls3) ->
                                                 let uu____4990 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____4990,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4870 with
                      | (match_tm,decls1) ->
                          let uu____5001 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____5001, decls1)))
and encode_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____5023 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5023
       then
         let uu____5024 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5024
       else ());
      (let uu____5026 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5026 with
       | (vars,pat_term) ->
           let uu____5036 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5059  ->
                     fun v1  ->
                       match uu____5059 with
                       | (env1,vars1) ->
                           let uu____5087 = gen_term_var env1 v1 in
                           (match uu____5087 with
                            | (xx,uu____5099,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____5036 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5146 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5147 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5148 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5154 =
                        let uu____5157 = encode_const c in
                        (scrutinee, uu____5157) in
                      FStar_SMTEncoding_Util.mkEq uu____5154
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5176 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5176 with
                        | (uu____5180,uu____5181::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5183 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5204  ->
                                  match uu____5204 with
                                  | (arg,uu____5210) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5220 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5220)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5240) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5259 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5274 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5296  ->
                                  match uu____5296 with
                                  | (arg,uu____5305) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5315 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5315)) in
                      FStar_All.pipe_right uu____5274 FStar_List.flatten in
                let pat_term1 uu____5331 = encode_term pat_term env1 in
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
      let uu____5338 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5353  ->
                fun uu____5354  ->
                  match (uu____5353, uu____5354) with
                  | ((tms,decls),(t,uu____5374)) ->
                      let uu____5385 = encode_term t env in
                      (match uu____5385 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5338 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5419 = FStar_Syntax_Util.list_elements e in
        match uu____5419 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5437 =
          let uu____5447 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5447 FStar_Syntax_Util.head_and_args in
        match uu____5437 with
        | (head1,args) ->
            let uu____5478 =
              let uu____5486 =
                let uu____5487 = FStar_Syntax_Util.un_uinst head1 in
                uu____5487.FStar_Syntax_Syntax.n in
              (uu____5486, args) in
            (match uu____5478 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5501,uu____5502)::(e,uu____5504)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> (e, None)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5535)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpatT_lid
                 -> (e, None)
             | uu____5556 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or t1 =
          let uu____5589 =
            let uu____5599 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5599 FStar_Syntax_Util.head_and_args in
          match uu____5589 with
          | (head1,args) ->
              let uu____5628 =
                let uu____5636 =
                  let uu____5637 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5637.FStar_Syntax_Syntax.n in
                (uu____5636, args) in
              (match uu____5628 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5650)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5670 -> None) in
        match elts with
        | t1::[] ->
            let uu____5688 = smt_pat_or t1 in
            (match uu____5688 with
             | Some e ->
                 let uu____5704 = list_elements1 e in
                 FStar_All.pipe_right uu____5704
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5721 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5721
                           (FStar_List.map one_pat)))
             | uu____5735 ->
                 let uu____5739 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5739])
        | uu____5770 ->
            let uu____5772 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5772] in
      let uu____5803 =
        let uu____5819 =
          let uu____5820 = FStar_Syntax_Subst.compress t in
          uu____5820.FStar_Syntax_Syntax.n in
        match uu____5819 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5850 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5850 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5885;
                        FStar_Syntax_Syntax.effect_name = uu____5886;
                        FStar_Syntax_Syntax.result_typ = uu____5887;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5889)::(post,uu____5891)::(pats,uu____5893)::[];
                        FStar_Syntax_Syntax.flags = uu____5894;_}
                      ->
                      let uu____5926 = lemma_pats pats in
                      (binders1, pre, post, uu____5926)
                  | uu____5945 -> failwith "impos"))
        | uu____5961 -> failwith "Impos" in
      match uu____5803 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___138_6006 = env in
            {
              bindings = (uu___138_6006.bindings);
              depth = (uu___138_6006.depth);
              tcenv = (uu___138_6006.tcenv);
              warn = (uu___138_6006.warn);
              cache = (uu___138_6006.cache);
              nolabels = (uu___138_6006.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___138_6006.encode_non_total_function_typ);
              current_module_name = (uu___138_6006.current_module_name)
            } in
          let uu____6007 = encode_binders None binders env1 in
          (match uu____6007 with
           | (vars,guards,env2,decls,uu____6022) ->
               let uu____6029 =
                 let uu____6036 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____6067 =
                             let uu____6072 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun uu____6088  ->
                                       match uu____6088 with
                                       | (t1,uu____6095) ->
                                           encode_term t1 env2)) in
                             FStar_All.pipe_right uu____6072 FStar_List.unzip in
                           match uu____6067 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____6036 FStar_List.unzip in
               (match uu____6029 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___139_6145 = env2 in
                      {
                        bindings = (uu___139_6145.bindings);
                        depth = (uu___139_6145.depth);
                        tcenv = (uu___139_6145.tcenv);
                        warn = (uu___139_6145.warn);
                        cache = (uu___139_6145.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___139_6145.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___139_6145.encode_non_total_function_typ);
                        current_module_name =
                          (uu___139_6145.current_module_name)
                      } in
                    let uu____6146 =
                      let uu____6149 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6149 env3 in
                    (match uu____6146 with
                     | (pre1,decls'') ->
                         let uu____6154 =
                           let uu____6157 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6157 env3 in
                         (match uu____6154 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6164 =
                                let uu____6165 =
                                  let uu____6171 =
                                    let uu____6172 =
                                      let uu____6175 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6175, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6172 in
                                  (pats, vars, uu____6171) in
                                FStar_SMTEncoding_Util.mkForall uu____6165 in
                              (uu____6164, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6188 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6188
        then
          let uu____6189 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6190 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6189 uu____6190
        else () in
      let enc f r l =
        let uu____6217 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6230 = encode_term (fst x) env in
                 match uu____6230 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6217 with
        | (decls,args) ->
            let uu____6247 =
              let uu___140_6248 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_6248.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_6248.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6247, decls) in
      let const_op f r uu____6267 = let uu____6270 = f r in (uu____6270, []) in
      let un_op f l =
        let uu____6286 = FStar_List.hd l in FStar_All.pipe_left f uu____6286 in
      let bin_op f uu___112_6299 =
        match uu___112_6299 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6307 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6334 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6343  ->
                 match uu____6343 with
                 | (t,uu____6351) ->
                     let uu____6352 = encode_formula t env in
                     (match uu____6352 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6334 with
        | (decls,phis) ->
            let uu____6369 =
              let uu___141_6370 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___141_6370.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___141_6370.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6369, decls) in
      let eq_op r uu___113_6386 =
        match uu___113_6386 with
        | uu____6389::e1::e2::[] ->
            let uu____6420 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6420 r [e1; e2]
        | uu____6439::uu____6440::e1::e2::[] ->
            let uu____6479 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6479 r [e1; e2]
        | l ->
            let uu____6499 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6499 r l in
      let mk_imp1 r uu___114_6518 =
        match uu___114_6518 with
        | (lhs,uu____6522)::(rhs,uu____6524)::[] ->
            let uu____6545 = encode_formula rhs env in
            (match uu____6545 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6554) ->
                      (l1, decls1)
                  | uu____6557 ->
                      let uu____6558 = encode_formula lhs env in
                      (match uu____6558 with
                       | (l2,decls2) ->
                           let uu____6565 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6565, (FStar_List.append decls1 decls2)))))
        | uu____6567 -> failwith "impossible" in
      let mk_ite r uu___115_6582 =
        match uu___115_6582 with
        | (guard,uu____6586)::(_then,uu____6588)::(_else,uu____6590)::[] ->
            let uu____6619 = encode_formula guard env in
            (match uu____6619 with
             | (g,decls1) ->
                 let uu____6626 = encode_formula _then env in
                 (match uu____6626 with
                  | (t,decls2) ->
                      let uu____6633 = encode_formula _else env in
                      (match uu____6633 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6642 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6661 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6661 in
      let connectives =
        let uu____6673 =
          let uu____6682 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6682) in
        let uu____6695 =
          let uu____6705 =
            let uu____6714 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6714) in
          let uu____6727 =
            let uu____6737 =
              let uu____6747 =
                let uu____6756 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6756) in
              let uu____6769 =
                let uu____6779 =
                  let uu____6789 =
                    let uu____6798 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6798) in
                  [uu____6789;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6779 in
              uu____6747 :: uu____6769 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6737 in
          uu____6705 :: uu____6727 in
        uu____6673 :: uu____6695 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6960 = encode_formula phi' env in
            (match uu____6960 with
             | (phi2,decls) ->
                 let uu____6967 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6967, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6968 ->
            let uu____6973 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6973 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____7002 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____7002 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____7010;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____7012;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____7028 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____7028 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____7060::(x,uu____7062)::(t,uu____7064)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____7098 = encode_term x env in
                 (match uu____7098 with
                  | (x1,decls) ->
                      let uu____7105 = encode_term t env in
                      (match uu____7105 with
                       | (t1,decls') ->
                           let uu____7112 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____7112, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____7116)::(msg,uu____7118)::(phi2,uu____7120)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____7154 =
                   let uu____7157 =
                     let uu____7158 = FStar_Syntax_Subst.compress r in
                     uu____7158.FStar_Syntax_Syntax.n in
                   let uu____7161 =
                     let uu____7162 = FStar_Syntax_Subst.compress msg in
                     uu____7162.FStar_Syntax_Syntax.n in
                   (uu____7157, uu____7161) in
                 (match uu____7154 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7169))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____7185 -> fallback phi2)
             | uu____7188 when head_redex env head2 ->
                 let uu____7196 = whnf env phi1 in
                 encode_formula uu____7196 env
             | uu____7197 ->
                 let uu____7205 = encode_term phi1 env in
                 (match uu____7205 with
                  | (tt,decls) ->
                      let uu____7212 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___142_7213 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___142_7213.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___142_7213.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7212, decls)))
        | uu____7216 ->
            let uu____7217 = encode_term phi1 env in
            (match uu____7217 with
             | (tt,decls) ->
                 let uu____7224 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___143_7225 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___143_7225.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___143_7225.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7224, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7252 = encode_binders None bs env1 in
        match uu____7252 with
        | (vars,guards,env2,decls,uu____7274) ->
            let uu____7281 =
              let uu____7288 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7311 =
                          let uu____7316 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7330  ->
                                    match uu____7330 with
                                    | (t,uu____7336) ->
                                        encode_term t
                                          (let uu___144_7337 = env2 in
                                           {
                                             bindings =
                                               (uu___144_7337.bindings);
                                             depth = (uu___144_7337.depth);
                                             tcenv = (uu___144_7337.tcenv);
                                             warn = (uu___144_7337.warn);
                                             cache = (uu___144_7337.cache);
                                             nolabels =
                                               (uu___144_7337.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___144_7337.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___144_7337.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7316 FStar_List.unzip in
                        match uu____7311 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7288 FStar_List.unzip in
            (match uu____7281 with
             | (pats,decls') ->
                 let uu____7389 = encode_formula body env2 in
                 (match uu____7389 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7408;
                             FStar_SMTEncoding_Term.rng = uu____7409;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7417 -> guards in
                      let uu____7420 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7420, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7454  ->
                   match uu____7454 with
                   | (x,uu____7458) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7464 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7470 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7470) uu____7464 tl1 in
             let uu____7472 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7484  ->
                       match uu____7484 with
                       | (b,uu____7488) ->
                           let uu____7489 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7489)) in
             (match uu____7472 with
              | None  -> ()
              | Some (x,uu____7493) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7503 =
                    let uu____7504 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7504 in
                  FStar_Errors.warn pos uu____7503) in
       let uu____7505 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7505 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7511 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7547  ->
                     match uu____7547 with
                     | (l,uu____7557) -> FStar_Ident.lid_equals op l)) in
           (match uu____7511 with
            | None  -> fallback phi1
            | Some (uu____7580,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7609 = encode_q_body env vars pats body in
             match uu____7609 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7635 =
                     let uu____7641 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7641) in
                   FStar_SMTEncoding_Term.mkForall uu____7635
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7653 = encode_q_body env vars pats body in
             match uu____7653 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7678 =
                   let uu____7679 =
                     let uu____7685 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7685) in
                   FStar_SMTEncoding_Term.mkExists uu____7679
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7678, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7734 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7734 with
  | (asym,a) ->
      let uu____7739 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7739 with
       | (xsym,x) ->
           let uu____7744 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7744 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7774 =
                      let uu____7780 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____7780, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7774 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7795 =
                      let uu____7799 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7799) in
                    FStar_SMTEncoding_Util.mkApp uu____7795 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7807 =
                    let uu____7809 =
                      let uu____7811 =
                        let uu____7813 =
                          let uu____7814 =
                            let uu____7818 =
                              let uu____7819 =
                                let uu____7825 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7825) in
                              FStar_SMTEncoding_Util.mkForall uu____7819 in
                            (uu____7818, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7814 in
                        let uu____7834 =
                          let uu____7836 =
                            let uu____7837 =
                              let uu____7841 =
                                let uu____7842 =
                                  let uu____7848 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7848) in
                                FStar_SMTEncoding_Util.mkForall uu____7842 in
                              (uu____7841,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7837 in
                          [uu____7836] in
                        uu____7813 :: uu____7834 in
                      xtok_decl :: uu____7811 in
                    xname_decl :: uu____7809 in
                  (xtok1, uu____7807) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7897 =
                    let uu____7905 =
                      let uu____7911 =
                        let uu____7912 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7912 in
                      quant axy uu____7911 in
                    (FStar_Syntax_Const.op_Eq, uu____7905) in
                  let uu____7918 =
                    let uu____7927 =
                      let uu____7935 =
                        let uu____7941 =
                          let uu____7942 =
                            let uu____7943 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7943 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7942 in
                        quant axy uu____7941 in
                      (FStar_Syntax_Const.op_notEq, uu____7935) in
                    let uu____7949 =
                      let uu____7958 =
                        let uu____7966 =
                          let uu____7972 =
                            let uu____7973 =
                              let uu____7974 =
                                let uu____7977 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7978 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7977, uu____7978) in
                              FStar_SMTEncoding_Util.mkLT uu____7974 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7973 in
                          quant xy uu____7972 in
                        (FStar_Syntax_Const.op_LT, uu____7966) in
                      let uu____7984 =
                        let uu____7993 =
                          let uu____8001 =
                            let uu____8007 =
                              let uu____8008 =
                                let uu____8009 =
                                  let uu____8012 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____8013 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____8012, uu____8013) in
                                FStar_SMTEncoding_Util.mkLTE uu____8009 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____8008 in
                            quant xy uu____8007 in
                          (FStar_Syntax_Const.op_LTE, uu____8001) in
                        let uu____8019 =
                          let uu____8028 =
                            let uu____8036 =
                              let uu____8042 =
                                let uu____8043 =
                                  let uu____8044 =
                                    let uu____8047 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____8048 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____8047, uu____8048) in
                                  FStar_SMTEncoding_Util.mkGT uu____8044 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____8043 in
                              quant xy uu____8042 in
                            (FStar_Syntax_Const.op_GT, uu____8036) in
                          let uu____8054 =
                            let uu____8063 =
                              let uu____8071 =
                                let uu____8077 =
                                  let uu____8078 =
                                    let uu____8079 =
                                      let uu____8082 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____8083 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____8082, uu____8083) in
                                    FStar_SMTEncoding_Util.mkGTE uu____8079 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____8078 in
                                quant xy uu____8077 in
                              (FStar_Syntax_Const.op_GTE, uu____8071) in
                            let uu____8089 =
                              let uu____8098 =
                                let uu____8106 =
                                  let uu____8112 =
                                    let uu____8113 =
                                      let uu____8114 =
                                        let uu____8117 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____8118 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____8117, uu____8118) in
                                      FStar_SMTEncoding_Util.mkSub uu____8114 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8113 in
                                  quant xy uu____8112 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____8106) in
                              let uu____8124 =
                                let uu____8133 =
                                  let uu____8141 =
                                    let uu____8147 =
                                      let uu____8148 =
                                        let uu____8149 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8149 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8148 in
                                    quant qx uu____8147 in
                                  (FStar_Syntax_Const.op_Minus, uu____8141) in
                                let uu____8155 =
                                  let uu____8164 =
                                    let uu____8172 =
                                      let uu____8178 =
                                        let uu____8179 =
                                          let uu____8180 =
                                            let uu____8183 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8184 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8183, uu____8184) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8180 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8179 in
                                      quant xy uu____8178 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8172) in
                                  let uu____8190 =
                                    let uu____8199 =
                                      let uu____8207 =
                                        let uu____8213 =
                                          let uu____8214 =
                                            let uu____8215 =
                                              let uu____8218 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8219 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8218, uu____8219) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8215 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8214 in
                                        quant xy uu____8213 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8207) in
                                    let uu____8225 =
                                      let uu____8234 =
                                        let uu____8242 =
                                          let uu____8248 =
                                            let uu____8249 =
                                              let uu____8250 =
                                                let uu____8253 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8254 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8253, uu____8254) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8250 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8249 in
                                          quant xy uu____8248 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8242) in
                                      let uu____8260 =
                                        let uu____8269 =
                                          let uu____8277 =
                                            let uu____8283 =
                                              let uu____8284 =
                                                let uu____8285 =
                                                  let uu____8288 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8289 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8288, uu____8289) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8285 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8284 in
                                            quant xy uu____8283 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8277) in
                                        let uu____8295 =
                                          let uu____8304 =
                                            let uu____8312 =
                                              let uu____8318 =
                                                let uu____8319 =
                                                  let uu____8320 =
                                                    let uu____8323 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8324 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8323, uu____8324) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8320 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8319 in
                                              quant xy uu____8318 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8312) in
                                          let uu____8330 =
                                            let uu____8339 =
                                              let uu____8347 =
                                                let uu____8353 =
                                                  let uu____8354 =
                                                    let uu____8355 =
                                                      let uu____8358 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8359 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8358,
                                                        uu____8359) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8355 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8354 in
                                                quant xy uu____8353 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8347) in
                                            let uu____8365 =
                                              let uu____8374 =
                                                let uu____8382 =
                                                  let uu____8388 =
                                                    let uu____8389 =
                                                      let uu____8390 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8390 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8389 in
                                                  quant qx uu____8388 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8382) in
                                              [uu____8374] in
                                            uu____8339 :: uu____8365 in
                                          uu____8304 :: uu____8330 in
                                        uu____8269 :: uu____8295 in
                                      uu____8234 :: uu____8260 in
                                    uu____8199 :: uu____8225 in
                                  uu____8164 :: uu____8190 in
                                uu____8133 :: uu____8155 in
                              uu____8098 :: uu____8124 in
                            uu____8063 :: uu____8089 in
                          uu____8028 :: uu____8054 in
                        uu____7993 :: uu____8019 in
                      uu____7958 :: uu____7984 in
                    uu____7927 :: uu____7949 in
                  uu____7897 :: uu____7918 in
                let mk1 l v1 =
                  let uu____8518 =
                    let uu____8523 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8555  ->
                              match uu____8555 with
                              | (l',uu____8564) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8523
                      (FStar_Option.map
                         (fun uu____8597  ->
                            match uu____8597 with | (uu____8608,b) -> b v1)) in
                  FStar_All.pipe_right uu____8518 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8649  ->
                          match uu____8649 with
                          | (l',uu____8658) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8684 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8684 with
        | (xxsym,xx) ->
            let uu____8689 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8689 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8697 =
                   let uu____8701 =
                     let uu____8702 =
                       let uu____8708 =
                         let uu____8709 =
                           let uu____8712 =
                             let uu____8713 =
                               let uu____8716 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8716) in
                             FStar_SMTEncoding_Util.mkEq uu____8713 in
                           (xx_has_type, uu____8712) in
                         FStar_SMTEncoding_Util.mkImp uu____8709 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8708) in
                     FStar_SMTEncoding_Util.mkForall uu____8702 in
                   let uu____8729 =
                     let uu____8730 =
                       let uu____8731 =
                         let uu____8732 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8732 in
                       Prims.strcat module_name uu____8731 in
                     varops.mk_unique uu____8730 in
                   (uu____8701, (Some "pretyping"), uu____8729) in
                 FStar_SMTEncoding_Util.mkAssume uu____8697)
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
    let uu____8762 =
      let uu____8763 =
        let uu____8767 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8767, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8763 in
    let uu____8769 =
      let uu____8771 =
        let uu____8772 =
          let uu____8776 =
            let uu____8777 =
              let uu____8783 =
                let uu____8784 =
                  let uu____8787 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8787) in
                FStar_SMTEncoding_Util.mkImp uu____8784 in
              ([[typing_pred]], [xx], uu____8783) in
            mkForall_fuel uu____8777 in
          (uu____8776, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8772 in
      [uu____8771] in
    uu____8762 :: uu____8769 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8815 =
      let uu____8816 =
        let uu____8820 =
          let uu____8821 =
            let uu____8827 =
              let uu____8830 =
                let uu____8832 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8832] in
              [uu____8830] in
            let uu____8835 =
              let uu____8836 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8836 tt in
            (uu____8827, [bb], uu____8835) in
          FStar_SMTEncoding_Util.mkForall uu____8821 in
        (uu____8820, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8816 in
    let uu____8847 =
      let uu____8849 =
        let uu____8850 =
          let uu____8854 =
            let uu____8855 =
              let uu____8861 =
                let uu____8862 =
                  let uu____8865 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8865) in
                FStar_SMTEncoding_Util.mkImp uu____8862 in
              ([[typing_pred]], [xx], uu____8861) in
            mkForall_fuel uu____8855 in
          (uu____8854, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8850 in
      [uu____8849] in
    uu____8815 :: uu____8847 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8899 =
        let uu____8900 =
          let uu____8904 =
            let uu____8906 =
              let uu____8908 =
                let uu____8910 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8911 =
                  let uu____8913 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8913] in
                uu____8910 :: uu____8911 in
              tt :: uu____8908 in
            tt :: uu____8906 in
          ("Prims.Precedes", uu____8904) in
        FStar_SMTEncoding_Util.mkApp uu____8900 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8899 in
    let precedes_y_x =
      let uu____8916 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8916 in
    let uu____8918 =
      let uu____8919 =
        let uu____8923 =
          let uu____8924 =
            let uu____8930 =
              let uu____8933 =
                let uu____8935 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8935] in
              [uu____8933] in
            let uu____8938 =
              let uu____8939 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8939 tt in
            (uu____8930, [bb], uu____8938) in
          FStar_SMTEncoding_Util.mkForall uu____8924 in
        (uu____8923, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8919 in
    let uu____8950 =
      let uu____8952 =
        let uu____8953 =
          let uu____8957 =
            let uu____8958 =
              let uu____8964 =
                let uu____8965 =
                  let uu____8968 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8968) in
                FStar_SMTEncoding_Util.mkImp uu____8965 in
              ([[typing_pred]], [xx], uu____8964) in
            mkForall_fuel uu____8958 in
          (uu____8957, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8953 in
      let uu____8981 =
        let uu____8983 =
          let uu____8984 =
            let uu____8988 =
              let uu____8989 =
                let uu____8995 =
                  let uu____8996 =
                    let uu____8999 =
                      let uu____9000 =
                        let uu____9002 =
                          let uu____9004 =
                            let uu____9006 =
                              let uu____9007 =
                                let uu____9010 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____9011 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____9010, uu____9011) in
                              FStar_SMTEncoding_Util.mkGT uu____9007 in
                            let uu____9012 =
                              let uu____9014 =
                                let uu____9015 =
                                  let uu____9018 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____9019 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____9018, uu____9019) in
                                FStar_SMTEncoding_Util.mkGTE uu____9015 in
                              let uu____9020 =
                                let uu____9022 =
                                  let uu____9023 =
                                    let uu____9026 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____9027 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____9026, uu____9027) in
                                  FStar_SMTEncoding_Util.mkLT uu____9023 in
                                [uu____9022] in
                              uu____9014 :: uu____9020 in
                            uu____9006 :: uu____9012 in
                          typing_pred_y :: uu____9004 in
                        typing_pred :: uu____9002 in
                      FStar_SMTEncoding_Util.mk_and_l uu____9000 in
                    (uu____8999, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8996 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8995) in
              mkForall_fuel uu____8989 in
            (uu____8988, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8984 in
        [uu____8983] in
      uu____8952 :: uu____8981 in
    uu____8918 :: uu____8950 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9057 =
      let uu____9058 =
        let uu____9062 =
          let uu____9063 =
            let uu____9069 =
              let uu____9072 =
                let uu____9074 = FStar_SMTEncoding_Term.boxString b in
                [uu____9074] in
              [uu____9072] in
            let uu____9077 =
              let uu____9078 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____9078 tt in
            (uu____9069, [bb], uu____9077) in
          FStar_SMTEncoding_Util.mkForall uu____9063 in
        (uu____9062, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9058 in
    let uu____9089 =
      let uu____9091 =
        let uu____9092 =
          let uu____9096 =
            let uu____9097 =
              let uu____9103 =
                let uu____9104 =
                  let uu____9107 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____9107) in
                FStar_SMTEncoding_Util.mkImp uu____9104 in
              ([[typing_pred]], [xx], uu____9103) in
            mkForall_fuel uu____9097 in
          (uu____9096, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9092 in
      [uu____9091] in
    uu____9057 :: uu____9089 in
  let mk_ref1 env reft_name uu____9129 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____9140 =
        let uu____9144 =
          let uu____9146 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9146] in
        (reft_name, uu____9144) in
      FStar_SMTEncoding_Util.mkApp uu____9140 in
    let refb =
      let uu____9149 =
        let uu____9153 =
          let uu____9155 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9155] in
        (reft_name, uu____9153) in
      FStar_SMTEncoding_Util.mkApp uu____9149 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9159 =
      let uu____9160 =
        let uu____9164 =
          let uu____9165 =
            let uu____9171 =
              let uu____9172 =
                let uu____9175 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9175) in
              FStar_SMTEncoding_Util.mkImp uu____9172 in
            ([[typing_pred]], [xx; aa], uu____9171) in
          mkForall_fuel uu____9165 in
        (uu____9164, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9160 in
    [uu____9159] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9215 =
      let uu____9216 =
        let uu____9220 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9220, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9216 in
    [uu____9215] in
  let mk_and_interp env conj uu____9231 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9248 =
      let uu____9249 =
        let uu____9253 =
          let uu____9254 =
            let uu____9260 =
              let uu____9261 =
                let uu____9264 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9264, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9261 in
            ([[l_and_a_b]], [aa; bb], uu____9260) in
          FStar_SMTEncoding_Util.mkForall uu____9254 in
        (uu____9253, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9249 in
    [uu____9248] in
  let mk_or_interp env disj uu____9288 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9305 =
      let uu____9306 =
        let uu____9310 =
          let uu____9311 =
            let uu____9317 =
              let uu____9318 =
                let uu____9321 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9321, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9318 in
            ([[l_or_a_b]], [aa; bb], uu____9317) in
          FStar_SMTEncoding_Util.mkForall uu____9311 in
        (uu____9310, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9306 in
    [uu____9305] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9362 =
      let uu____9363 =
        let uu____9367 =
          let uu____9368 =
            let uu____9374 =
              let uu____9375 =
                let uu____9378 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9378, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9375 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9374) in
          FStar_SMTEncoding_Util.mkForall uu____9368 in
        (uu____9367, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9363 in
    [uu____9362] in
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
    let uu____9425 =
      let uu____9426 =
        let uu____9430 =
          let uu____9431 =
            let uu____9437 =
              let uu____9438 =
                let uu____9441 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9441, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9438 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9437) in
          FStar_SMTEncoding_Util.mkForall uu____9431 in
        (uu____9430, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9426 in
    [uu____9425] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9486 =
      let uu____9487 =
        let uu____9491 =
          let uu____9492 =
            let uu____9498 =
              let uu____9499 =
                let uu____9502 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9502, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9499 in
            ([[l_imp_a_b]], [aa; bb], uu____9498) in
          FStar_SMTEncoding_Util.mkForall uu____9492 in
        (uu____9491, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9487 in
    [uu____9486] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9543 =
      let uu____9544 =
        let uu____9548 =
          let uu____9549 =
            let uu____9555 =
              let uu____9556 =
                let uu____9559 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9559, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9556 in
            ([[l_iff_a_b]], [aa; bb], uu____9555) in
          FStar_SMTEncoding_Util.mkForall uu____9549 in
        (uu____9548, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9544 in
    [uu____9543] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9593 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9593 in
    let uu____9595 =
      let uu____9596 =
        let uu____9600 =
          let uu____9601 =
            let uu____9607 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9607) in
          FStar_SMTEncoding_Util.mkForall uu____9601 in
        (uu____9600, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9596 in
    [uu____9595] in
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
      let uu____9647 =
        let uu____9651 =
          let uu____9653 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9653] in
        ("Valid", uu____9651) in
      FStar_SMTEncoding_Util.mkApp uu____9647 in
    let uu____9655 =
      let uu____9656 =
        let uu____9660 =
          let uu____9661 =
            let uu____9667 =
              let uu____9668 =
                let uu____9671 =
                  let uu____9672 =
                    let uu____9678 =
                      let uu____9681 =
                        let uu____9683 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9683] in
                      [uu____9681] in
                    let uu____9686 =
                      let uu____9687 =
                        let uu____9690 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9690, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9687 in
                    (uu____9678, [xx1], uu____9686) in
                  FStar_SMTEncoding_Util.mkForall uu____9672 in
                (uu____9671, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9668 in
            ([[l_forall_a_b]], [aa; bb], uu____9667) in
          FStar_SMTEncoding_Util.mkForall uu____9661 in
        (uu____9660, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9656 in
    [uu____9655] in
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
      let uu____9741 =
        let uu____9745 =
          let uu____9747 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9747] in
        ("Valid", uu____9745) in
      FStar_SMTEncoding_Util.mkApp uu____9741 in
    let uu____9749 =
      let uu____9750 =
        let uu____9754 =
          let uu____9755 =
            let uu____9761 =
              let uu____9762 =
                let uu____9765 =
                  let uu____9766 =
                    let uu____9772 =
                      let uu____9775 =
                        let uu____9777 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9777] in
                      [uu____9775] in
                    let uu____9780 =
                      let uu____9781 =
                        let uu____9784 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9784, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9781 in
                    (uu____9772, [xx1], uu____9780) in
                  FStar_SMTEncoding_Util.mkExists uu____9766 in
                (uu____9765, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9762 in
            ([[l_exists_a_b]], [aa; bb], uu____9761) in
          FStar_SMTEncoding_Util.mkForall uu____9755 in
        (uu____9754, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9750 in
    [uu____9749] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9820 =
      let uu____9821 =
        let uu____9825 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9826 = varops.mk_unique "typing_range_const" in
        (uu____9825, (Some "Range_const typing"), uu____9826) in
      FStar_SMTEncoding_Util.mkAssume uu____9821 in
    [uu____9820] in
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
          let uu____10088 =
            FStar_Util.find_opt
              (fun uu____10106  ->
                 match uu____10106 with
                 | (l,uu____10116) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____10088 with
          | None  -> []
          | Some (uu____10138,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10175 = encode_function_type_as_formula t env in
        match uu____10175 with
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
            let uu____10207 =
              (let uu____10208 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10208) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10207
            then
              let uu____10212 = new_term_constant_and_tok_from_lid env lid in
              match uu____10212 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10224 =
                      let uu____10225 = FStar_Syntax_Subst.compress t_norm in
                      uu____10225.FStar_Syntax_Syntax.n in
                    match uu____10224 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10230) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10247  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10250 -> [] in
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
              (let uu____10259 = prims.is lid in
               if uu____10259
               then
                 let vname = varops.new_fvar lid in
                 let uu____10264 = prims.mk lid vname in
                 match uu____10264 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10279 =
                    let uu____10285 = curried_arrow_formals_comp t_norm in
                    match uu____10285 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10296 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10296
                          then
                            let uu____10297 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___145_10298 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___145_10298.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___145_10298.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___145_10298.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___145_10298.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___145_10298.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___145_10298.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___145_10298.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___145_10298.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___145_10298.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___145_10298.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___145_10298.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___145_10298.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___145_10298.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___145_10298.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___145_10298.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___145_10298.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___145_10298.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___145_10298.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___145_10298.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___145_10298.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___145_10298.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___145_10298.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___145_10298.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___145_10298.FStar_TypeChecker_Env.proof_ns)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10297
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10305 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10305)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10279 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10332 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10332 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10345 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___116_10369  ->
                                     match uu___116_10369 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10372 =
                                           FStar_Util.prefix vars in
                                         (match uu____10372 with
                                          | (uu____10383,(xxsym,uu____10385))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10395 =
                                                let uu____10396 =
                                                  let uu____10400 =
                                                    let uu____10401 =
                                                      let uu____10407 =
                                                        let uu____10408 =
                                                          let uu____10411 =
                                                            let uu____10412 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10412 in
                                                          (vapp, uu____10411) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10408 in
                                                      ([[vapp]], vars,
                                                        uu____10407) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10401 in
                                                  (uu____10400,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10396 in
                                              [uu____10395])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10423 =
                                           FStar_Util.prefix vars in
                                         (match uu____10423 with
                                          | (uu____10434,(xxsym,uu____10436))
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
                                              let uu____10450 =
                                                let uu____10451 =
                                                  let uu____10455 =
                                                    let uu____10456 =
                                                      let uu____10462 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10462) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10456 in
                                                  (uu____10455,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10451 in
                                              [uu____10450])
                                     | uu____10471 -> [])) in
                           let uu____10472 = encode_binders None formals env1 in
                           (match uu____10472 with
                            | (vars,guards,env',decls1,uu____10488) ->
                                let uu____10495 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10500 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10500, decls1)
                                  | Some p ->
                                      let uu____10502 = encode_formula p env' in
                                      (match uu____10502 with
                                       | (g,ds) ->
                                           let uu____10509 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10509,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10495 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10518 =
                                         let uu____10522 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10522) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10518 in
                                     let uu____10527 =
                                       let vname_decl =
                                         let uu____10532 =
                                           let uu____10538 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10543  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10538,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10532 in
                                       let uu____10548 =
                                         let env2 =
                                           let uu___146_10552 = env1 in
                                           {
                                             bindings =
                                               (uu___146_10552.bindings);
                                             depth = (uu___146_10552.depth);
                                             tcenv = (uu___146_10552.tcenv);
                                             warn = (uu___146_10552.warn);
                                             cache = (uu___146_10552.cache);
                                             nolabels =
                                               (uu___146_10552.nolabels);
                                             use_zfuel_name =
                                               (uu___146_10552.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___146_10552.current_module_name)
                                           } in
                                         let uu____10553 =
                                           let uu____10554 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10554 in
                                         if uu____10553
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10548 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10564::uu____10565 ->
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
                                                   let uu____10588 =
                                                     let uu____10594 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10594) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10588 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10608 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10610 =
                                             match formals with
                                             | [] ->
                                                 let uu____10619 =
                                                   let uu____10620 =
                                                     let uu____10622 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10622 in
                                                   push_free_var env1 lid
                                                     vname uu____10620 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10619)
                                             | uu____10625 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10630 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10630 in
                                                 let name_tok_corr =
                                                   let uu____10632 =
                                                     let uu____10636 =
                                                       let uu____10637 =
                                                         let uu____10643 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10643) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10637 in
                                                     (uu____10636,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10632 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10610 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10527 with
                                      | (decls2,env2) ->
                                          let uu____10667 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10672 =
                                              encode_term res_t1 env' in
                                            match uu____10672 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10680 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10680,
                                                  decls) in
                                          (match uu____10667 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10688 =
                                                   let uu____10692 =
                                                     let uu____10693 =
                                                       let uu____10699 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10699) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10693 in
                                                   (uu____10692,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10688 in
                                               let freshness =
                                                 let uu____10708 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10708
                                                 then
                                                   let uu____10711 =
                                                     let uu____10712 =
                                                       let uu____10718 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
                                                       let uu____10724 =
                                                         varops.next_id () in
                                                       (vname, uu____10718,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10724) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10712 in
                                                   let uu____10726 =
                                                     let uu____10728 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10728] in
                                                   uu____10711 :: uu____10726
                                                 else [] in
                                               let g =
                                                 let uu____10732 =
                                                   let uu____10734 =
                                                     let uu____10736 =
                                                       let uu____10738 =
                                                         let uu____10740 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10740 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10738 in
                                                     FStar_List.append decls3
                                                       uu____10736 in
                                                   FStar_List.append decls2
                                                     uu____10734 in
                                                 FStar_List.append decls11
                                                   uu____10732 in
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
          let uu____10762 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10762 with
          | None  ->
              let uu____10785 = encode_free_var env x t t_norm [] in
              (match uu____10785 with
               | (decls,env1) ->
                   let uu____10800 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10800 with
                    | (n1,x',uu____10819) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10831) -> ((n1, x1), [], env)
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
          let uu____10864 = encode_free_var env lid t tt quals in
          match uu____10864 with
          | (decls,env1) ->
              let uu____10875 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10875
              then
                let uu____10879 =
                  let uu____10881 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10881 in
                (uu____10879, env1)
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
             (fun uu____10909  ->
                fun lb  ->
                  match uu____10909 with
                  | (decls,env1) ->
                      let uu____10921 =
                        let uu____10925 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10925
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10921 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10939 = FStar_Syntax_Util.head_and_args t in
    match uu____10939 with
    | (hd1,args) ->
        let uu____10965 =
          let uu____10966 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10966.FStar_Syntax_Syntax.n in
        (match uu____10965 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10970,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10983 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10998  ->
      fun quals  ->
        match uu____10998 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____11048 = FStar_Util.first_N nbinders formals in
              match uu____11048 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11090  ->
                         fun uu____11091  ->
                           match (uu____11090, uu____11091) with
                           | ((formal,uu____11101),(binder,uu____11103)) ->
                               let uu____11108 =
                                 let uu____11113 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11113) in
                               FStar_Syntax_Syntax.NT uu____11108) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11118 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11132  ->
                              match uu____11132 with
                              | (x,i) ->
                                  let uu____11139 =
                                    let uu___147_11140 = x in
                                    let uu____11141 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___147_11140.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___147_11140.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11141
                                    } in
                                  (uu____11139, i))) in
                    FStar_All.pipe_right uu____11118
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11153 =
                      let uu____11155 =
                        let uu____11156 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11156.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____11155 in
                    let uu____11160 =
                      let uu____11161 = FStar_Syntax_Subst.compress body in
                      let uu____11162 =
                        let uu____11163 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11163 in
                      FStar_Syntax_Syntax.extend_app_n uu____11161
                        uu____11162 in
                    uu____11160 uu____11153 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11205 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11205
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___148_11206 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___148_11206.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___148_11206.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___148_11206.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___148_11206.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___148_11206.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___148_11206.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___148_11206.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___148_11206.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___148_11206.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___148_11206.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___148_11206.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___148_11206.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___148_11206.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___148_11206.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___148_11206.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___148_11206.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___148_11206.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___148_11206.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___148_11206.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___148_11206.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___148_11206.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___148_11206.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___148_11206.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___148_11206.FStar_TypeChecker_Env.proof_ns)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11227 = FStar_Syntax_Util.abs_formals e in
                match uu____11227 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11276::uu____11277 ->
                         let uu____11285 =
                           let uu____11286 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11286.FStar_Syntax_Syntax.n in
                         (match uu____11285 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11313 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11313 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11341 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11341
                                   then
                                     let uu____11364 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11364 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11412  ->
                                                   fun uu____11413  ->
                                                     match (uu____11412,
                                                             uu____11413)
                                                     with
                                                     | ((x,uu____11423),
                                                        (b,uu____11425)) ->
                                                         let uu____11430 =
                                                           let uu____11435 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11435) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11430)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11437 =
                                            let uu____11448 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11448) in
                                          (uu____11437, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11488 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11488 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11540) ->
                              let uu____11545 =
                                let uu____11556 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____11556 in
                              (uu____11545, true)
                          | uu____11589 when Prims.op_Negation norm1 ->
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
                          | uu____11591 ->
                              let uu____11592 =
                                let uu____11593 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11594 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11593
                                  uu____11594 in
                              failwith uu____11592)
                     | uu____11607 ->
                         let uu____11608 =
                           let uu____11609 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11609.FStar_Syntax_Syntax.n in
                         (match uu____11608 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11636 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11636 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11654 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11654 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11702 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11730 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11730
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11737 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11778  ->
                            fun lb  ->
                              match uu____11778 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11829 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11829
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11832 =
                                      let uu____11840 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11840
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11832 with
                                    | (tok,decl,env2) ->
                                        let uu____11865 =
                                          let uu____11872 =
                                            let uu____11878 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11878, tok) in
                                          uu____11872 :: toks in
                                        (uu____11865, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11737 with
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
                        | uu____11980 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11985 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11985 vars)
                            else
                              (let uu____11987 =
                                 let uu____11991 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11991) in
                               FStar_SMTEncoding_Util.mkApp uu____11987) in
                      let uu____11996 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___117_11998  ->
                                 match uu___117_11998 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11999 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____12002 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____12002))) in
                      if uu____11996
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____12022;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____12024;
                                FStar_Syntax_Syntax.lbeff = uu____12025;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____12066 =
                                 let uu____12070 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____12070 with
                                 | (tcenv',uu____12081,e_t) ->
                                     let uu____12085 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12092 -> failwith "Impossible" in
                                     (match uu____12085 with
                                      | (e1,t_norm1) ->
                                          ((let uu___151_12101 = env1 in
                                            {
                                              bindings =
                                                (uu___151_12101.bindings);
                                              depth = (uu___151_12101.depth);
                                              tcenv = tcenv';
                                              warn = (uu___151_12101.warn);
                                              cache = (uu___151_12101.cache);
                                              nolabels =
                                                (uu___151_12101.nolabels);
                                              use_zfuel_name =
                                                (uu___151_12101.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___151_12101.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___151_12101.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____12066 with
                                | (env',e1,t_norm1) ->
                                    let uu____12108 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____12108 with
                                     | ((binders,body,uu____12120,uu____12121),curry)
                                         ->
                                         ((let uu____12128 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____12128
                                           then
                                             let uu____12129 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12130 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12129 uu____12130
                                           else ());
                                          (let uu____12132 =
                                             encode_binders None binders env' in
                                           match uu____12132 with
                                           | (vars,guards,env'1,binder_decls,uu____12148)
                                               ->
                                               let body1 =
                                                 let uu____12156 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12156
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12159 =
                                                 let uu____12164 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12164
                                                 then
                                                   let uu____12170 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12171 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12170, uu____12171)
                                                 else
                                                   (let uu____12177 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12177)) in
                                               (match uu____12159 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12191 =
                                                        let uu____12195 =
                                                          let uu____12196 =
                                                            let uu____12202 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12202) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12196 in
                                                        let uu____12208 =
                                                          let uu____12210 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12210 in
                                                        (uu____12195,
                                                          uu____12208,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12191 in
                                                    let uu____12212 =
                                                      let uu____12214 =
                                                        let uu____12216 =
                                                          let uu____12218 =
                                                            let uu____12220 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12220 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12218 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12216 in
                                                      FStar_List.append
                                                        decls1 uu____12214 in
                                                    (uu____12212, env1))))))
                           | uu____12223 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12242 = varops.fresh "fuel" in
                             (uu____12242, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12245 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12284  ->
                                     fun uu____12285  ->
                                       match (uu____12284, uu____12285) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12367 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12367 in
                                           let gtok =
                                             let uu____12369 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12369 in
                                           let env3 =
                                             let uu____12371 =
                                               let uu____12373 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12373 in
                                             push_free_var env2 flid gtok
                                               uu____12371 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12245 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12459
                                 t_norm uu____12461 =
                                 match (uu____12459, uu____12461) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12488;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12489;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12506 =
                                       let uu____12510 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12510 with
                                       | (tcenv',uu____12525,e_t) ->
                                           let uu____12529 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12536 ->
                                                 failwith "Impossible" in
                                           (match uu____12529 with
                                            | (e1,t_norm1) ->
                                                ((let uu___152_12545 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___152_12545.bindings);
                                                    depth =
                                                      (uu___152_12545.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___152_12545.warn);
                                                    cache =
                                                      (uu___152_12545.cache);
                                                    nolabels =
                                                      (uu___152_12545.nolabels);
                                                    use_zfuel_name =
                                                      (uu___152_12545.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___152_12545.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___152_12545.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12506 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12555 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12555
                                            then
                                              let uu____12556 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12557 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12558 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12556 uu____12557
                                                uu____12558
                                            else ());
                                           (let uu____12560 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12560 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12582 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12582
                                                  then
                                                    let uu____12583 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12584 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12585 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12586 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12583 uu____12584
                                                      uu____12585 uu____12586
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12590 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12590 with
                                                  | (vars,guards,env'1,binder_decls,uu____12608)
                                                      ->
                                                      let decl_g =
                                                        let uu____12616 =
                                                          let uu____12622 =
                                                            let uu____12624 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12624 in
                                                          (g, uu____12622,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12616 in
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
                                                        let uu____12639 =
                                                          let uu____12643 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12643) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12639 in
                                                      let gsapp =
                                                        let uu____12649 =
                                                          let uu____12653 =
                                                            let uu____12655 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12655 ::
                                                              vars_tm in
                                                          (g, uu____12653) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12649 in
                                                      let gmax =
                                                        let uu____12659 =
                                                          let uu____12663 =
                                                            let uu____12665 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12665 ::
                                                              vars_tm in
                                                          (g, uu____12663) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12659 in
                                                      let body1 =
                                                        let uu____12669 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12669
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12671 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12671 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12682
                                                               =
                                                               let uu____12686
                                                                 =
                                                                 let uu____12687
                                                                   =
                                                                   let uu____12695
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
                                                                    uu____12695) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12687 in
                                                               let uu____12706
                                                                 =
                                                                 let uu____12708
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12708 in
                                                               (uu____12686,
                                                                 uu____12706,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12682 in
                                                           let eqn_f =
                                                             let uu____12711
                                                               =
                                                               let uu____12715
                                                                 =
                                                                 let uu____12716
                                                                   =
                                                                   let uu____12722
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12722) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12716 in
                                                               (uu____12715,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12711 in
                                                           let eqn_g' =
                                                             let uu____12730
                                                               =
                                                               let uu____12734
                                                                 =
                                                                 let uu____12735
                                                                   =
                                                                   let uu____12741
                                                                    =
                                                                    let uu____12742
                                                                    =
                                                                    let uu____12745
                                                                    =
                                                                    let uu____12746
                                                                    =
                                                                    let uu____12750
                                                                    =
                                                                    let uu____12752
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12752
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12750) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12746 in
                                                                    (gsapp,
                                                                    uu____12745) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12742 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12741) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12735 in
                                                               (uu____12734,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12730 in
                                                           let uu____12764 =
                                                             let uu____12769
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12769
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12786)
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
                                                                    let uu____12801
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12801
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12804
                                                                    =
                                                                    let uu____12808
                                                                    =
                                                                    let uu____12809
                                                                    =
                                                                    let uu____12815
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12815) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12809 in
                                                                    (uu____12808,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12804 in
                                                                 let uu____12826
                                                                   =
                                                                   let uu____12830
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12830
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12838
                                                                    =
                                                                    let uu____12840
                                                                    =
                                                                    let uu____12841
                                                                    =
                                                                    let uu____12845
                                                                    =
                                                                    let uu____12846
                                                                    =
                                                                    let uu____12852
                                                                    =
                                                                    let uu____12853
                                                                    =
                                                                    let uu____12856
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12856,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12853 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12852) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12846 in
                                                                    (uu____12845,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12841 in
                                                                    [uu____12840] in
                                                                    (d3,
                                                                    uu____12838) in
                                                                 (match uu____12826
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12764
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
                               let uu____12891 =
                                 let uu____12898 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12934  ->
                                      fun uu____12935  ->
                                        match (uu____12934, uu____12935) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____13021 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____13021 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12898 in
                               (match uu____12891 with
                                | (decls2,eqns,env01) ->
                                    let uu____13061 =
                                      let isDeclFun uu___118_13069 =
                                        match uu___118_13069 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____13070 -> true
                                        | uu____13076 -> false in
                                      let uu____13077 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____13077
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____13061 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____13104 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____13104
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
        let uu____13137 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13137 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____13140 = encode_sigelt' env se in
      match uu____13140 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13150 =
                  let uu____13151 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13151 in
                [uu____13150]
            | uu____13152 ->
                let uu____13153 =
                  let uu____13155 =
                    let uu____13156 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13156 in
                  uu____13155 :: g in
                let uu____13157 =
                  let uu____13159 =
                    let uu____13160 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13160 in
                  [uu____13159] in
                FStar_List.append uu____13153 uu____13157 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13168 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13171 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13173 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13175 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13183 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13186 =
            let uu____13187 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13187 Prims.op_Negation in
          if uu____13186
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13207 ->
                   let uu____13208 =
                     let uu____13211 =
                       let uu____13212 =
                         let uu____13227 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13227) in
                       FStar_Syntax_Syntax.Tm_abs uu____13212 in
                     FStar_Syntax_Syntax.mk uu____13211 in
                   uu____13208 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13280 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13280 with
               | (aname,atok,env2) ->
                   let uu____13290 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13290 with
                    | (formals,uu____13300) ->
                        let uu____13307 =
                          let uu____13310 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13310 env2 in
                        (match uu____13307 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13318 =
                                 let uu____13319 =
                                   let uu____13325 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13333  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13325,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13319 in
                               [uu____13318;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13340 =
                               let aux uu____13369 uu____13370 =
                                 match (uu____13369, uu____13370) with
                                 | ((bv,uu____13397),(env3,acc_sorts,acc)) ->
                                     let uu____13418 = gen_term_var env3 bv in
                                     (match uu____13418 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13340 with
                              | (uu____13456,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13470 =
                                      let uu____13474 =
                                        let uu____13475 =
                                          let uu____13481 =
                                            let uu____13482 =
                                              let uu____13485 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13485) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13482 in
                                          ([[app]], xs_sorts, uu____13481) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13475 in
                                      (uu____13474, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13470 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13497 =
                                      let uu____13501 =
                                        let uu____13502 =
                                          let uu____13508 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13508) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13502 in
                                      (uu____13501,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13497 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13518 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13518 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13534,uu____13535)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13536 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13536 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13547,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13552 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___119_13554  ->
                      match uu___119_13554 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13555 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13558 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13559 -> false)) in
            Prims.op_Negation uu____13552 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13565 = encode_top_level_val env fv t quals in
             match uu____13565 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13577 =
                   let uu____13579 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13579 in
                 (uu____13577, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13584 = encode_formula f env in
          (match uu____13584 with
           | (f1,decls) ->
               let g =
                 let uu____13593 =
                   let uu____13594 =
                     let uu____13598 =
                       let uu____13600 =
                         let uu____13601 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13601 in
                       Some uu____13600 in
                     let uu____13602 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13598, uu____13602) in
                   FStar_SMTEncoding_Util.mkAssume uu____13594 in
                 [uu____13593] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13606,uu____13607) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13613 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13620 =
                       let uu____13625 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13625.FStar_Syntax_Syntax.fv_name in
                     uu____13620.FStar_Syntax_Syntax.v in
                   let uu____13629 =
                     let uu____13630 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13630 in
                   if uu____13629
                   then
                     let val_decl =
                       let uu___153_13645 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___153_13645.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___153_13645.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___153_13645.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13649 = encode_sigelt' env1 val_decl in
                     match uu____13649 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____13613 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13666,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13668;
                          FStar_Syntax_Syntax.lbtyp = uu____13669;
                          FStar_Syntax_Syntax.lbeff = uu____13670;
                          FStar_Syntax_Syntax.lbdef = uu____13671;_}::[]),uu____13672,uu____13673)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13687 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13687 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13710 =
                   let uu____13712 =
                     let uu____13713 =
                       let uu____13717 =
                         let uu____13718 =
                           let uu____13724 =
                             let uu____13725 =
                               let uu____13728 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13728) in
                             FStar_SMTEncoding_Util.mkEq uu____13725 in
                           ([[b2t_x]], [xx], uu____13724) in
                         FStar_SMTEncoding_Util.mkForall uu____13718 in
                       (uu____13717, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13713 in
                   [uu____13712] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13710 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13745,uu____13746,uu____13747)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___120_13753  ->
                  match uu___120_13753 with
                  | FStar_Syntax_Syntax.Discriminator uu____13754 -> true
                  | uu____13755 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13757,lids,uu____13759) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13766 =
                     let uu____13767 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13767.FStar_Ident.idText in
                   uu____13766 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___121_13769  ->
                     match uu___121_13769 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13770 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13773,uu____13774)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___122_13784  ->
                  match uu___122_13784 with
                  | FStar_Syntax_Syntax.Projector uu____13785 -> true
                  | uu____13788 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13795 = try_lookup_free_var env l in
          (match uu____13795 with
           | Some uu____13799 -> ([], env)
           | None  ->
               let se1 =
                 let uu___154_13802 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___154_13802.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___154_13802.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13808,uu____13809) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13821) ->
          let uu____13826 = encode_sigelts env ses in
          (match uu____13826 with
           | (g,env1) ->
               let uu____13836 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___123_13846  ->
                         match uu___123_13846 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13847;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13848;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13849;_}
                             -> false
                         | uu____13851 -> true)) in
               (match uu____13836 with
                | (g',inversions) ->
                    let uu____13860 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___124_13870  ->
                              match uu___124_13870 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13871 ->
                                  true
                              | uu____13877 -> false)) in
                    (match uu____13860 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13888,tps,k,uu____13891,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___125_13901  ->
                    match uu___125_13901 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13902 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13909 = c in
              match uu____13909 with
              | (name,args,uu____13913,uu____13914,uu____13915) ->
                  let uu____13918 =
                    let uu____13919 =
                      let uu____13925 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13932  ->
                                match uu____13932 with
                                | (uu____13936,sort,uu____13938) -> sort)) in
                      (name, uu____13925, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13919 in
                  [uu____13918]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13956 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13959 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13959 FStar_Option.isNone)) in
            if uu____13956
            then []
            else
              (let uu____13976 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13976 with
               | (xxsym,xx) ->
                   let uu____13982 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13993  ->
                             fun l  ->
                               match uu____13993 with
                               | (out,decls) ->
                                   let uu____14005 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____14005 with
                                    | (uu____14011,data_t) ->
                                        let uu____14013 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____14013 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____14042 =
                                                 let uu____14043 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____14043.FStar_Syntax_Syntax.n in
                                               match uu____14042 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____14051,indices) ->
                                                   indices
                                               | uu____14067 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____14079  ->
                                                         match uu____14079
                                                         with
                                                         | (x,uu____14083) ->
                                                             let uu____14084
                                                               =
                                                               let uu____14085
                                                                 =
                                                                 let uu____14089
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____14089,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14085 in
                                                             push_term_var
                                                               env1 x
                                                               uu____14084)
                                                    env) in
                                             let uu____14091 =
                                               encode_args indices env1 in
                                             (match uu____14091 with
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
                                                      let uu____14115 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14123
                                                                 =
                                                                 let uu____14126
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____14126,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14123)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____14115
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____14128 =
                                                      let uu____14129 =
                                                        let uu____14132 =
                                                          let uu____14133 =
                                                            let uu____14136 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____14136,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14133 in
                                                        (out, uu____14132) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14129 in
                                                    (uu____14128,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13982 with
                    | (data_ax,decls) ->
                        let uu____14144 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14144 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14158 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14158 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14161 =
                                 let uu____14165 =
                                   let uu____14166 =
                                     let uu____14172 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14180 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14172,
                                       uu____14180) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14166 in
                                 let uu____14188 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14165, (Some "inversion axiom"),
                                   uu____14188) in
                               FStar_SMTEncoding_Util.mkAssume uu____14161 in
                             let pattern_guarded_inversion =
                               let uu____14192 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14192
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14203 =
                                   let uu____14204 =
                                     let uu____14208 =
                                       let uu____14209 =
                                         let uu____14215 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14223 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14215, uu____14223) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14209 in
                                     let uu____14231 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14208, (Some "inversion axiom"),
                                       uu____14231) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14204 in
                                 [uu____14203]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14234 =
            let uu____14242 =
              let uu____14243 = FStar_Syntax_Subst.compress k in
              uu____14243.FStar_Syntax_Syntax.n in
            match uu____14242 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14272 -> (tps, k) in
          (match uu____14234 with
           | (formals,res) ->
               let uu____14287 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14287 with
                | (formals1,res1) ->
                    let uu____14294 = encode_binders None formals1 env in
                    (match uu____14294 with
                     | (vars,guards,env',binder_decls,uu____14309) ->
                         let uu____14316 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14316 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14329 =
                                  let uu____14333 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14333) in
                                FStar_SMTEncoding_Util.mkApp uu____14329 in
                              let uu____14338 =
                                let tname_decl =
                                  let uu____14344 =
                                    let uu____14345 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14360  ->
                                              match uu____14360 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14368 = varops.next_id () in
                                    (tname, uu____14345,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14368, false) in
                                  constructor_or_logic_type_decl uu____14344 in
                                let uu____14373 =
                                  match vars with
                                  | [] ->
                                      let uu____14380 =
                                        let uu____14381 =
                                          let uu____14383 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14383 in
                                        push_free_var env1 t tname
                                          uu____14381 in
                                      ([], uu____14380)
                                  | uu____14387 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14393 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14393 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14402 =
                                          let uu____14406 =
                                            let uu____14407 =
                                              let uu____14415 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14415) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14407 in
                                          (uu____14406,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14402 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14373 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14338 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14438 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14438 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14455 =
                                               let uu____14456 =
                                                 let uu____14460 =
                                                   let uu____14461 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14461 in
                                                 (uu____14460,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14456 in
                                             [uu____14455]
                                           else [] in
                                         let uu____14464 =
                                           let uu____14466 =
                                             let uu____14468 =
                                               let uu____14469 =
                                                 let uu____14473 =
                                                   let uu____14474 =
                                                     let uu____14480 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14480) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14474 in
                                                 (uu____14473, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14469 in
                                             [uu____14468] in
                                           FStar_List.append karr uu____14466 in
                                         FStar_List.append decls1 uu____14464 in
                                   let aux =
                                     let uu____14489 =
                                       let uu____14491 =
                                         inversion_axioms tapp vars in
                                       let uu____14493 =
                                         let uu____14495 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14495] in
                                       FStar_List.append uu____14491
                                         uu____14493 in
                                     FStar_List.append kindingAx uu____14489 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14500,uu____14501,uu____14502,uu____14503,uu____14504)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14509,t,uu____14511,n_tps,uu____14513) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14518 = new_term_constant_and_tok_from_lid env d in
          (match uu____14518 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14529 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14529 with
                | (formals,t_res) ->
                    let uu____14551 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14551 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14560 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14560 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14598 =
                                            mk_term_projector_name d x in
                                          (uu____14598,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14600 =
                                  let uu____14610 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14610, true) in
                                FStar_All.pipe_right uu____14600
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
                              let uu____14632 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14632 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14640::uu____14641 ->
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
                                         let uu____14666 =
                                           let uu____14672 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14672) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14666
                                     | uu____14685 -> tok_typing in
                                   let uu____14690 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14690 with
                                    | (vars',guards',env'',decls_formals,uu____14705)
                                        ->
                                        let uu____14712 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14712 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14731 ->
                                                   let uu____14735 =
                                                     let uu____14736 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14736 in
                                                   [uu____14735] in
                                             let encode_elim uu____14743 =
                                               let uu____14744 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14744 with
                                               | (head1,args) ->
                                                   let uu____14773 =
                                                     let uu____14774 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14774.FStar_Syntax_Syntax.n in
                                                   (match uu____14773 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____14781;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14782;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14783;_},uu____14784)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14794 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14794
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
                                                                 | uu____14820
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14828
                                                                    =
                                                                    let uu____14829
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14829 in
                                                                    if
                                                                    uu____14828
                                                                    then
                                                                    let uu____14836
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14836]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14838
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14851
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14851
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14873
                                                                    =
                                                                    let uu____14877
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14877 in
                                                                    (match uu____14873
                                                                    with
                                                                    | 
                                                                    (uu____14884,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14890
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14890
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14892
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14892
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
                                                             (match uu____14838
                                                              with
                                                              | (uu____14900,arg_vars,elim_eqns_or_guards,uu____14903)
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
                                                                    let uu____14922
                                                                    =
                                                                    let uu____14926
                                                                    =
                                                                    let uu____14927
                                                                    =
                                                                    let uu____14933
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14939
                                                                    =
                                                                    let uu____14940
                                                                    =
                                                                    let uu____14943
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14943) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14940 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14933,
                                                                    uu____14939) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14927 in
                                                                    (uu____14926,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14922 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14956
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14956,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14958
                                                                    =
                                                                    let uu____14962
                                                                    =
                                                                    let uu____14963
                                                                    =
                                                                    let uu____14969
                                                                    =
                                                                    let uu____14972
                                                                    =
                                                                    let uu____14974
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14974] in
                                                                    [uu____14972] in
                                                                    let uu____14977
                                                                    =
                                                                    let uu____14978
                                                                    =
                                                                    let uu____14981
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14982
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14981,
                                                                    uu____14982) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14978 in
                                                                    (uu____14969,
                                                                    [x],
                                                                    uu____14977) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14963 in
                                                                    let uu____14992
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14962,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14992) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14958
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14997
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
                                                                    (let uu____15012
                                                                    =
                                                                    let uu____15013
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15013
                                                                    dapp1 in
                                                                    [uu____15012]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14997
                                                                    FStar_List.flatten in
                                                                    let uu____15017
                                                                    =
                                                                    let uu____15021
                                                                    =
                                                                    let uu____15022
                                                                    =
                                                                    let uu____15028
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15034
                                                                    =
                                                                    let uu____15035
                                                                    =
                                                                    let uu____15038
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15038) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15035 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15028,
                                                                    uu____15034) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15022 in
                                                                    (uu____15021,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15017) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____15054 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15054
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
                                                                 | uu____15080
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15088
                                                                    =
                                                                    let uu____15089
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15089 in
                                                                    if
                                                                    uu____15088
                                                                    then
                                                                    let uu____15096
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15096]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15098
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15111
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15111
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15133
                                                                    =
                                                                    let uu____15137
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15137 in
                                                                    (match uu____15133
                                                                    with
                                                                    | 
                                                                    (uu____15144,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15150
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15150
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15152
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15152
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
                                                             (match uu____15098
                                                              with
                                                              | (uu____15160,arg_vars,elim_eqns_or_guards,uu____15163)
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
                                                                    let uu____15182
                                                                    =
                                                                    let uu____15186
                                                                    =
                                                                    let uu____15187
                                                                    =
                                                                    let uu____15193
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15199
                                                                    =
                                                                    let uu____15200
                                                                    =
                                                                    let uu____15203
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15203) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15200 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15193,
                                                                    uu____15199) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15187 in
                                                                    (uu____15186,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15182 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15216
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15216,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15218
                                                                    =
                                                                    let uu____15222
                                                                    =
                                                                    let uu____15223
                                                                    =
                                                                    let uu____15229
                                                                    =
                                                                    let uu____15232
                                                                    =
                                                                    let uu____15234
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15234] in
                                                                    [uu____15232] in
                                                                    let uu____15237
                                                                    =
                                                                    let uu____15238
                                                                    =
                                                                    let uu____15241
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15242
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15241,
                                                                    uu____15242) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15238 in
                                                                    (uu____15229,
                                                                    [x],
                                                                    uu____15237) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15223 in
                                                                    let uu____15252
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15222,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15252) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15218
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15257
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
                                                                    (let uu____15272
                                                                    =
                                                                    let uu____15273
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15273
                                                                    dapp1 in
                                                                    [uu____15272]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15257
                                                                    FStar_List.flatten in
                                                                    let uu____15277
                                                                    =
                                                                    let uu____15281
                                                                    =
                                                                    let uu____15282
                                                                    =
                                                                    let uu____15288
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15294
                                                                    =
                                                                    let uu____15295
                                                                    =
                                                                    let uu____15298
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15298) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15295 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15288,
                                                                    uu____15294) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15282 in
                                                                    (uu____15281,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15277) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15308 ->
                                                        ((let uu____15310 =
                                                            let uu____15311 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15312 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15311
                                                              uu____15312 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15310);
                                                         ([], []))) in
                                             let uu____15315 = encode_elim () in
                                             (match uu____15315 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15327 =
                                                      let uu____15329 =
                                                        let uu____15331 =
                                                          let uu____15333 =
                                                            let uu____15335 =
                                                              let uu____15336
                                                                =
                                                                let uu____15342
                                                                  =
                                                                  let uu____15344
                                                                    =
                                                                    let uu____15345
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15345 in
                                                                  Some
                                                                    uu____15344 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15342) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15336 in
                                                            [uu____15335] in
                                                          let uu____15348 =
                                                            let uu____15350 =
                                                              let uu____15352
                                                                =
                                                                let uu____15354
                                                                  =
                                                                  let uu____15356
                                                                    =
                                                                    let uu____15358
                                                                    =
                                                                    let uu____15360
                                                                    =
                                                                    let uu____15361
                                                                    =
                                                                    let uu____15365
                                                                    =
                                                                    let uu____15366
                                                                    =
                                                                    let uu____15372
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15372) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15366 in
                                                                    (uu____15365,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15361 in
                                                                    let uu____15379
                                                                    =
                                                                    let uu____15381
                                                                    =
                                                                    let uu____15382
                                                                    =
                                                                    let uu____15386
                                                                    =
                                                                    let uu____15387
                                                                    =
                                                                    let uu____15393
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____15399
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15393,
                                                                    uu____15399) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15387 in
                                                                    (uu____15386,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15382 in
                                                                    [uu____15381] in
                                                                    uu____15360
                                                                    ::
                                                                    uu____15379 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15358 in
                                                                  FStar_List.append
                                                                    uu____15356
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15354 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15352 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15350 in
                                                          FStar_List.append
                                                            uu____15333
                                                            uu____15348 in
                                                        FStar_List.append
                                                          decls3 uu____15331 in
                                                      FStar_List.append
                                                        decls2 uu____15329 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15327 in
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
           (fun uu____15420  ->
              fun se  ->
                match uu____15420 with
                | (g,env1) ->
                    let uu____15432 = encode_sigelt env1 se in
                    (match uu____15432 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15468 =
        match uu____15468 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15486 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____15491 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15491
                   then
                     let uu____15492 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15493 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15494 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15492 uu____15493 uu____15494
                   else ());
                  (let uu____15496 = encode_term t1 env1 in
                   match uu____15496 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15506 =
                         let uu____15510 =
                           let uu____15511 =
                             let uu____15512 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15512
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15511 in
                         new_term_constant_from_string env1 x uu____15510 in
                       (match uu____15506 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15523 = FStar_Options.log_queries () in
                              if uu____15523
                              then
                                let uu____15525 =
                                  let uu____15526 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15527 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15528 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15526 uu____15527 uu____15528 in
                                Some uu____15525
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15539,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15548 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15548 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15561,se,uu____15563) ->
                 let uu____15566 = encode_sigelt env1 se in
                 (match uu____15566 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15576,se) ->
                 let uu____15580 = encode_sigelt env1 se in
                 (match uu____15580 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15590 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15590 with | (uu____15602,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15647  ->
            match uu____15647 with
            | (l,uu____15654,uu____15655) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15676  ->
            match uu____15676 with
            | (l,uu____15684,uu____15685) ->
                let uu____15690 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39) (
                    fst l) in
                let uu____15691 =
                  let uu____15693 =
                    let uu____15694 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15694 in
                  [uu____15693] in
                uu____15690 :: uu____15691)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15705 =
      let uu____15707 =
        let uu____15708 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15710 =
          let uu____15711 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15711 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15708;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15710
        } in
      [uu____15707] in
    FStar_ST.write last_env uu____15705
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15721 = FStar_ST.read last_env in
      match uu____15721 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15727 ->
          let uu___155_15729 = e in
          let uu____15730 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___155_15729.bindings);
            depth = (uu___155_15729.depth);
            tcenv;
            warn = (uu___155_15729.warn);
            cache = (uu___155_15729.cache);
            nolabels = (uu___155_15729.nolabels);
            use_zfuel_name = (uu___155_15729.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_15729.encode_non_total_function_typ);
            current_module_name = uu____15730
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15734 = FStar_ST.read last_env in
    match uu____15734 with
    | [] -> failwith "Empty env stack"
    | uu____15739::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15747  ->
    let uu____15748 = FStar_ST.read last_env in
    match uu____15748 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___156_15759 = hd1 in
          {
            bindings = (uu___156_15759.bindings);
            depth = (uu___156_15759.depth);
            tcenv = (uu___156_15759.tcenv);
            warn = (uu___156_15759.warn);
            cache = refs;
            nolabels = (uu___156_15759.nolabels);
            use_zfuel_name = (uu___156_15759.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___156_15759.encode_non_total_function_typ);
            current_module_name = (uu___156_15759.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15765  ->
    let uu____15766 = FStar_ST.read last_env in
    match uu____15766 with
    | [] -> failwith "Popping an empty stack"
    | uu____15771::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15779  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15782  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15785  ->
    let uu____15786 = FStar_ST.read last_env in
    match uu____15786 with
    | hd1::uu____15792::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15798 -> failwith "Impossible"
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
        | (uu____15847::uu____15848,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___157_15852 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___157_15852.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___157_15852.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___157_15852.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15853 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15864 =
        let uu____15866 =
          let uu____15867 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15867 in
        let uu____15868 = open_fact_db_tags env in uu____15866 :: uu____15868 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15864
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
      let uu____15883 = encode_sigelt env se in
      match uu____15883 with
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
        let uu____15908 = FStar_Options.log_queries () in
        if uu____15908
        then
          let uu____15910 =
            let uu____15911 =
              let uu____15912 =
                let uu____15913 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15913 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15912 in
            FStar_SMTEncoding_Term.Caption uu____15911 in
          uu____15910 :: decls
        else decls in
      let env =
        let uu____15920 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15920 tcenv in
      let uu____15921 = encode_top_level_facts env se in
      match uu____15921 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15930 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15930))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15941 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15941
       then
         let uu____15942 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15942
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15965  ->
                 fun se  ->
                   match uu____15965 with
                   | (g,env2) ->
                       let uu____15977 = encode_top_level_facts env2 se in
                       (match uu____15977 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15990 =
         encode_signature
           (let uu___158_15994 = env in
            {
              bindings = (uu___158_15994.bindings);
              depth = (uu___158_15994.depth);
              tcenv = (uu___158_15994.tcenv);
              warn = false;
              cache = (uu___158_15994.cache);
              nolabels = (uu___158_15994.nolabels);
              use_zfuel_name = (uu___158_15994.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___158_15994.encode_non_total_function_typ);
              current_module_name = (uu___158_15994.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15990 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____16006 = FStar_Options.log_queries () in
             if uu____16006
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___159_16011 = env1 in
               {
                 bindings = (uu___159_16011.bindings);
                 depth = (uu___159_16011.depth);
                 tcenv = (uu___159_16011.tcenv);
                 warn = true;
                 cache = (uu___159_16011.cache);
                 nolabels = (uu___159_16011.nolabels);
                 use_zfuel_name = (uu___159_16011.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___159_16011.encode_non_total_function_typ);
                 current_module_name = (uu___159_16011.current_module_name)
               });
            (let uu____16013 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____16013
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
        (let uu____16048 =
           let uu____16049 = FStar_TypeChecker_Env.current_module tcenv in
           uu____16049.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16048);
        (let env =
           let uu____16051 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____16051 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____16058 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16079 = aux rest in
                 (match uu____16079 with
                  | (out,rest1) ->
                      let t =
                        let uu____16097 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____16097 with
                        | Some uu____16101 ->
                            let uu____16102 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16102
                              x.FStar_Syntax_Syntax.sort
                        | uu____16103 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____16106 =
                        let uu____16108 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___160_16109 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___160_16109.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___160_16109.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16108 :: out in
                      (uu____16106, rest1))
             | uu____16112 -> ([], bindings1) in
           let uu____16116 = aux bindings in
           match uu____16116 with
           | (closing,bindings1) ->
               let uu____16130 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16130, bindings1) in
         match uu____16058 with
         | (q1,bindings1) ->
             let uu____16143 =
               let uu____16146 =
                 FStar_List.filter
                   (fun uu___126_16148  ->
                      match uu___126_16148 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16149 ->
                          false
                      | uu____16153 -> true) bindings1 in
               encode_env_bindings env uu____16146 in
             (match uu____16143 with
              | (env_decls,env1) ->
                  ((let uu____16164 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16164
                    then
                      let uu____16165 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16165
                    else ());
                   (let uu____16167 = encode_formula q1 env1 in
                    match uu____16167 with
                    | (phi,qdecls) ->
                        let uu____16179 =
                          let uu____16182 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16182 phi in
                        (match uu____16179 with
                         | (labels,phi1) ->
                             let uu____16192 = encode_labels labels in
                             (match uu____16192 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____16213 =
                                      let uu____16217 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16218 =
                                        varops.mk_unique "@query" in
                                      (uu____16217, (Some "query"),
                                        uu____16218) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16213 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16231 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16231 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16233 = encode_formula q env in
       match uu____16233 with
       | (f,uu____16237) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16239) -> true
             | uu____16242 -> false)))