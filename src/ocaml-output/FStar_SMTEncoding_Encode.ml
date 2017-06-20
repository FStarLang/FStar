open Prims
let add_fuel x tl1 =
  let uu____16 = FStar_Options.unthrottle_inductives () in
  if uu____16 then tl1 else x :: tl1
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___101_77  ->
       match uu___101_77 with
       | (FStar_Util.Inl uu____82,uu____83) -> false
       | uu____86 -> true) args
let subst_lcomp_opt s l =
  match l with
  | Some (FStar_Util.Inl l1) ->
      let uu____117 =
        let uu____120 =
          let uu____121 =
            let uu____124 = l1.FStar_Syntax_Syntax.comp () in
            FStar_Syntax_Subst.subst_comp s uu____124 in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____121 in
        FStar_Util.Inl uu____120 in
      Some uu____117
  | uu____129 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_'
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___126_143 = a in
        let uu____144 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____144;
          FStar_Syntax_Syntax.index =
            (uu___126_143.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___126_143.FStar_Syntax_Syntax.sort)
        } in
      let uu____145 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____145
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____158 =
          let uu____159 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____159 in
        let uu____160 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____160 with
        | (uu____163,t) ->
            let uu____165 =
              let uu____166 = FStar_Syntax_Subst.compress t in
              uu____166.FStar_Syntax_Syntax.n in
            (match uu____165 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____181 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____181 with
                  | (binders,uu____185) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid (fst b)))
             | uu____196 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____203 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____203
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____210 =
        let uu____213 = mk_term_projector_name lid a in
        (uu____213,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____210
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____220 =
        let uu____223 = mk_term_projector_name_by_pos lid i in
        (uu____223,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____220
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
  let new_scope uu____436 =
    let uu____437 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____439 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____437, uu____439) in
  let scopes =
    let uu____450 = let uu____456 = new_scope () in [uu____456] in
    FStar_Util.mk_ref uu____450 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____481 =
        let uu____483 = FStar_ST.read scopes in
        FStar_Util.find_map uu____483
          (fun uu____503  ->
             match uu____503 with
             | (names1,uu____510) -> FStar_Util.smap_try_find names1 y1) in
      match uu____481 with
      | None  -> y1
      | Some uu____515 ->
          (FStar_Util.incr ctr;
           (let uu____520 =
              let uu____521 =
                let uu____522 = FStar_ST.read ctr in
                Prims.string_of_int uu____522 in
              Prims.strcat "__" uu____521 in
            Prims.strcat y1 uu____520)) in
    let top_scope =
      let uu____527 =
        let uu____532 = FStar_ST.read scopes in FStar_List.hd uu____532 in
      FStar_All.pipe_left FStar_Pervasives.fst uu____527 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____571 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____582 =
      let uu____583 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____583 in
    FStar_Util.format2 "%s_%s" pfx uu____582 in
  let string_const s =
    let uu____588 =
      let uu____590 = FStar_ST.read scopes in
      FStar_Util.find_map uu____590
        (fun uu____610  ->
           match uu____610 with
           | (uu____616,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____588 with
    | Some f -> f
    | None  ->
        let id = next_id1 () in
        let f =
          let uu____625 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____625 in
        let top_scope =
          let uu____628 =
            let uu____633 = FStar_ST.read scopes in FStar_List.hd uu____633 in
          FStar_All.pipe_left FStar_Pervasives.snd uu____628 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____661 =
    let uu____662 =
      let uu____668 = new_scope () in
      let uu____673 = FStar_ST.read scopes in uu____668 :: uu____673 in
    FStar_ST.write scopes uu____662 in
  let pop1 uu____700 =
    let uu____701 =
      let uu____707 = FStar_ST.read scopes in FStar_List.tl uu____707 in
    FStar_ST.write scopes uu____701 in
  let mark1 uu____734 = push1 () in
  let reset_mark1 uu____738 = pop1 () in
  let commit_mark1 uu____742 =
    let uu____743 = FStar_ST.read scopes in
    match uu____743 with
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
    | uu____809 -> failwith "Impossible" in
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
    let uu___127_818 = x in
    let uu____819 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____819;
      FStar_Syntax_Syntax.index = (uu___127_818.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___127_818.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term option* FStar_SMTEncoding_Term.term option)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____842 -> false
let __proj__Binding_var__item___0:
  binding -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____866 -> false
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
         (fun uu___102_1056  ->
            match uu___102_1056 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1059 -> [])) in
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
    let uu____1067 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___103_1074  ->
              match uu___103_1074 with
              | Binding_var (x,uu____1076) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1078,uu____1079,uu____1080) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1067 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string option =
  fun env  ->
    fun t  ->
      let uu____1113 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1113
      then
        let uu____1115 = FStar_Syntax_Print.term_to_string t in
        Some uu____1115
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1126 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1126)
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
        (let uu___128_1139 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___128_1139.tcenv);
           warn = (uu___128_1139.warn);
           cache = (uu___128_1139.cache);
           nolabels = (uu___128_1139.nolabels);
           use_zfuel_name = (uu___128_1139.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_1139.encode_non_total_function_typ);
           current_module_name = (uu___128_1139.current_module_name)
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
        (let uu___129_1153 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___129_1153.depth);
           tcenv = (uu___129_1153.tcenv);
           warn = (uu___129_1153.warn);
           cache = (uu___129_1153.cache);
           nolabels = (uu___129_1153.nolabels);
           use_zfuel_name = (uu___129_1153.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___129_1153.encode_non_total_function_typ);
           current_module_name = (uu___129_1153.current_module_name)
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
          (let uu___130_1170 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___130_1170.depth);
             tcenv = (uu___130_1170.tcenv);
             warn = (uu___130_1170.warn);
             cache = (uu___130_1170.cache);
             nolabels = (uu___130_1170.nolabels);
             use_zfuel_name = (uu___130_1170.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___130_1170.encode_non_total_function_typ);
             current_module_name = (uu___130_1170.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___131_1180 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___131_1180.depth);
          tcenv = (uu___131_1180.tcenv);
          warn = (uu___131_1180.warn);
          cache = (uu___131_1180.cache);
          nolabels = (uu___131_1180.nolabels);
          use_zfuel_name = (uu___131_1180.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_1180.encode_non_total_function_typ);
          current_module_name = (uu___131_1180.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___104_1199  ->
             match uu___104_1199 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1207 -> None) in
      let uu____1210 = aux a in
      match uu____1210 with
      | None  ->
          let a2 = unmangle a in
          let uu____1217 = aux a2 in
          (match uu____1217 with
           | None  ->
               let uu____1223 =
                 let uu____1224 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1225 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1224 uu____1225 in
               failwith uu____1223
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1245 =
        let uu___132_1246 = env in
        let uu____1247 =
          let uu____1249 =
            let uu____1250 =
              let uu____1257 =
                let uu____1259 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1259 in
              (x, fname, uu____1257, None) in
            Binding_fvar uu____1250 in
          uu____1249 :: (env.bindings) in
        {
          bindings = uu____1247;
          depth = (uu___132_1246.depth);
          tcenv = (uu___132_1246.tcenv);
          warn = (uu___132_1246.warn);
          cache = (uu___132_1246.cache);
          nolabels = (uu___132_1246.nolabels);
          use_zfuel_name = (uu___132_1246.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___132_1246.encode_non_total_function_typ);
          current_module_name = (uu___132_1246.current_module_name)
        } in
      (fname, ftok, uu____1245)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option) option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___105_1286  ->
           match uu___105_1286 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1308 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1320 =
        lookup_binding env
          (fun uu___106_1327  ->
             match uu___106_1327 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1337 -> None) in
      FStar_All.pipe_right uu____1320 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option)
  =
  fun env  ->
    fun a  ->
      let uu____1350 = try_lookup_lid env a in
      match uu____1350 with
      | None  ->
          let uu____1367 =
            let uu____1368 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1368 in
          failwith uu____1367
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
          let uu___133_1399 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___133_1399.depth);
            tcenv = (uu___133_1399.tcenv);
            warn = (uu___133_1399.warn);
            cache = (uu___133_1399.cache);
            nolabels = (uu___133_1399.nolabels);
            use_zfuel_name = (uu___133_1399.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_1399.encode_non_total_function_typ);
            current_module_name = (uu___133_1399.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1411 = lookup_lid env x in
        match uu____1411 with
        | (t1,t2,uu____1419) ->
            let t3 =
              let uu____1425 =
                let uu____1429 =
                  let uu____1431 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1431] in
                (f, uu____1429) in
              FStar_SMTEncoding_Util.mkApp uu____1425 in
            let uu___134_1434 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___134_1434.depth);
              tcenv = (uu___134_1434.tcenv);
              warn = (uu___134_1434.warn);
              cache = (uu___134_1434.cache);
              nolabels = (uu___134_1434.nolabels);
              use_zfuel_name = (uu___134_1434.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_1434.encode_non_total_function_typ);
              current_module_name = (uu___134_1434.current_module_name)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term option =
  fun env  ->
    fun l  ->
      let uu____1444 = try_lookup_lid env l in
      match uu____1444 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1471 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1476,fuel::[]) ->
                         let uu____1479 =
                           let uu____1480 =
                             let uu____1481 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1481
                               FStar_Pervasives.fst in
                           FStar_Util.starts_with uu____1480 "fuel" in
                         if uu____1479
                         then
                           let uu____1483 =
                             let uu____1484 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1484
                               fuel in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1483
                         else Some t
                     | uu____1487 -> Some t)
                | uu____1488 -> None))
let lookup_free_var:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____1498 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____1498 with
      | Some t -> t
      | None  ->
          let uu____1501 =
            let uu____1502 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____1502 in
          failwith uu____1501
let lookup_free_var_name:
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____1511 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____1511 with | (x,uu____1518,uu____1519) -> x
let lookup_free_var_sym:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op* FStar_SMTEncoding_Term.term Prims.list)
  =
  fun env  ->
    fun a  ->
      let uu____1535 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____1535 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____1556;
                 FStar_SMTEncoding_Term.rng = uu____1557;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____1565 ->
               (match sym with
                | None  -> ((FStar_SMTEncoding_Term.Var name), [])
                | Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____1579 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name: env_t -> Prims.string -> FStar_SMTEncoding_Term.term option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___107_1593  ->
           match uu___107_1593 with
           | Binding_fvar (uu____1595,nm',tok,uu____1598) when nm = nm' ->
               tok
           | uu____1603 -> None)
let mkForall_fuel' n1 uu____1620 =
  match uu____1620 with
  | (pats,vars,body) ->
      let fallback uu____1636 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1639 = FStar_Options.unthrottle_inductives () in
      if uu____1639
      then fallback ()
      else
        (let uu____1641 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1641 with
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
                       | uu____1662 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1676 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1676
                     | uu____1678 ->
                         let uu____1679 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1679 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1682 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____1708 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____1716 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____1721 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____1722 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____1733 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____1748 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1750 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1750 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____1760;
             FStar_Syntax_Syntax.pos = uu____1761;
             FStar_Syntax_Syntax.vars = uu____1762;_},uu____1763)
          ->
          let uu____1778 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1778 FStar_Option.isNone
      | uu____1787 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1794 =
        let uu____1795 = FStar_Syntax_Util.un_uinst t in
        uu____1795.FStar_Syntax_Syntax.n in
      match uu____1794 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1798,uu____1799,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___108_1829  ->
                  match uu___108_1829 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1830 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1831,uu____1832,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1859 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1859 FStar_Option.isSome
      | uu____1868 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1875 = head_normal env t in
      if uu____1875
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
    let uu____1886 =
      let uu____1887 = FStar_Syntax_Syntax.null_binder t in [uu____1887] in
    let uu____1888 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1886 uu____1888 None
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
                    let uu____1918 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1918
                | s ->
                    let uu____1922 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1922) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___109_1934  ->
    match uu___109_1934 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1935 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____1963;
                       FStar_SMTEncoding_Term.rng = uu____1964;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1978) ->
              let uu____1983 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1996 -> false) args (FStar_List.rev xs)) in
              if uu____1983 then tok_of_name env f else None
          | (uu____1999,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____2002 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____2006 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____2006)) in
              if uu____2002 then Some t else None
          | uu____2009 -> None in
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
    | uu____2100 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___110_2103  ->
    match uu___110_2103 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2105 =
          let uu____2109 =
            let uu____2111 =
              let uu____2112 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2112 in
            [uu____2111] in
          ("FStar.Char.Char", uu____2109) in
        FStar_SMTEncoding_Util.mkApp uu____2105
    | FStar_Const.Const_int (i,None ) ->
        let uu____2120 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2120
    | FStar_Const.Const_int (i,Some uu____2122) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2131) ->
        let uu____2134 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2134
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2138 =
          let uu____2139 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2139 in
        failwith uu____2138
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2158 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2166 ->
            let uu____2171 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2171
        | uu____2172 ->
            if norm1
            then let uu____2173 = whnf env t1 in aux false uu____2173
            else
              (let uu____2175 =
                 let uu____2176 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2177 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2176 uu____2177 in
               failwith uu____2175) in
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
    | uu____2198 ->
        let uu____2199 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2199)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2227::uu____2228::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Syntax_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2231::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2233 -> false
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
        (let uu____2371 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2371
         then
           let uu____2372 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2372
         else ());
        (let uu____2374 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2423  ->
                   fun b  ->
                     match uu____2423 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2466 =
                           let x = unmangle (fst b) in
                           let uu____2475 = gen_term_var env1 x in
                           match uu____2475 with
                           | (xxsym,xx,env') ->
                               let uu____2489 =
                                 let uu____2492 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2492 env1 xx in
                               (match uu____2489 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2466 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2374 with
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
          let uu____2580 = encode_term t env in
          match uu____2580 with
          | (t1,decls) ->
              let uu____2587 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2587, decls)
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
          let uu____2595 = encode_term t env in
          match uu____2595 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2604 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2604, decls)
               | Some f ->
                   let uu____2606 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2606, decls))
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
        let uu____2612 = encode_args args_e env in
        match uu____2612 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2624 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____2631 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____2631 in
            let binary arg_tms1 =
              let uu____2640 =
                let uu____2641 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____2641 in
              let uu____2642 =
                let uu____2643 =
                  let uu____2644 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2644 in
                FStar_SMTEncoding_Term.unboxInt uu____2643 in
              (uu____2640, uu____2642) in
            let mk_default uu____2649 =
              let uu____2650 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2650 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____2691 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2691
              then
                let uu____2692 = let uu____2693 = mk_args ts in op uu____2693 in
                FStar_All.pipe_right uu____2692 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____2716 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____2716
              then
                let uu____2717 = binary ts in
                match uu____2717 with
                | (t1,t2) ->
                    let uu____2722 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____2722
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2725 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____2725
                 then
                   let uu____2726 = op (binary ts) in
                   FStar_All.pipe_right uu____2726
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
            let uu____2816 =
              let uu____2822 =
                FStar_List.tryFind
                  (fun uu____2837  ->
                     match uu____2837 with
                     | (l,uu____2844) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____2822 FStar_Util.must in
            (match uu____2816 with
             | (uu____2869,op) ->
                 let uu____2877 = op arg_tms in (uu____2877, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2884 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2884
       then
         let uu____2885 = FStar_Syntax_Print.tag_of_term t in
         let uu____2886 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2887 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2885 uu____2886
           uu____2887
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2891 ->
           let uu____2912 =
             let uu____2913 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2914 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2915 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2916 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2913
               uu____2914 uu____2915 uu____2916 in
           failwith uu____2912
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2919 =
             let uu____2920 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2921 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2922 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2923 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2920
               uu____2921 uu____2922 uu____2923 in
           failwith uu____2919
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2927 =
             let uu____2928 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2928 in
           failwith uu____2927
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2933) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2963) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2972 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2972, [])
       | FStar_Syntax_Syntax.Tm_type uu____2974 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2977) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2983 = encode_const c in (uu____2983, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2998 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2998 with
            | (binders1,res) ->
                let uu____3005 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____3005
                then
                  let uu____3008 = encode_binders None binders1 env in
                  (match uu____3008 with
                   | (vars,guards,env',decls,uu____3023) ->
                       let fsym =
                         let uu____3033 = varops.fresh "f" in
                         (uu____3033, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____3036 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_3042 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_3042.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_3042.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_3042.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_3042.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_3042.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_3042.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_3042.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_3042.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_3042.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_3042.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_3042.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_3042.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_3042.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_3042.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_3042.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_3042.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_3042.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_3042.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_3042.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_3042.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_3042.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_3042.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_3042.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____3036 with
                        | (pre_opt,res_t) ->
                            let uu____3049 =
                              encode_term_pred None res_t env' app in
                            (match uu____3049 with
                             | (res_pred,decls') ->
                                 let uu____3056 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____3063 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____3063, [])
                                   | Some pre ->
                                       let uu____3066 =
                                         encode_formula pre env' in
                                       (match uu____3066 with
                                        | (guard,decls0) ->
                                            let uu____3074 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3074, decls0)) in
                                 (match uu____3056 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3082 =
                                          let uu____3088 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3088) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3082 in
                                      let cvars =
                                        let uu____3098 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3098
                                          (FStar_List.filter
                                             (fun uu____3107  ->
                                                match uu____3107 with
                                                | (x,uu____3111) ->
                                                    x <> (fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3122 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3122 with
                                       | Some cache_entry ->
                                           let uu____3127 =
                                             let uu____3128 =
                                               let uu____3132 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3132) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3128 in
                                           (uu____3127,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____3143 =
                                               let uu____3144 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3144 in
                                             varops.mk_unique uu____3143 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars in
                                           let caption =
                                             let uu____3151 =
                                               FStar_Options.log_queries () in
                                             if uu____3151
                                             then
                                               let uu____3153 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____3153
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3159 =
                                               let uu____3163 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3163) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3159 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3171 =
                                               let uu____3175 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3175, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3171 in
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
                                             let uu____3188 =
                                               let uu____3192 =
                                                 let uu____3193 =
                                                   let uu____3199 =
                                                     let uu____3200 =
                                                       let uu____3203 =
                                                         let uu____3204 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3204 in
                                                       (f_has_t, uu____3203) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3200 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3199) in
                                                 mkForall_fuel uu____3193 in
                                               (uu____3192,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3188 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3217 =
                                               let uu____3221 =
                                                 let uu____3222 =
                                                   let uu____3228 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3228) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3222 in
                                               (uu____3221, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3217 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3242 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3242);
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
                     let uu____3253 =
                       let uu____3257 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3257, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3253 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3266 =
                       let uu____3270 =
                         let uu____3271 =
                           let uu____3277 =
                             let uu____3278 =
                               let uu____3281 =
                                 let uu____3282 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3282 in
                               (f_has_t, uu____3281) in
                             FStar_SMTEncoding_Util.mkImp uu____3278 in
                           ([[f_has_t]], [fsym], uu____3277) in
                         mkForall_fuel uu____3271 in
                       (uu____3270, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3266 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3296 ->
           let uu____3301 =
             let uu____3304 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3304 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3309;
                 FStar_Syntax_Syntax.pos = uu____3310;
                 FStar_Syntax_Syntax.vars = uu____3311;_} ->
                 let uu____3318 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____3318 with
                  | (b,f1) ->
                      let uu____3332 =
                        let uu____3333 = FStar_List.hd b in fst uu____3333 in
                      (uu____3332, f1))
             | uu____3338 -> failwith "impossible" in
           (match uu____3301 with
            | (x,f) ->
                let uu____3345 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3345 with
                 | (base_t,decls) ->
                     let uu____3352 = gen_term_var env x in
                     (match uu____3352 with
                      | (x1,xtm,env') ->
                          let uu____3361 = encode_formula f env' in
                          (match uu____3361 with
                           | (refinement,decls') ->
                               let uu____3368 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3368 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3379 =
                                        let uu____3381 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3385 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3381
                                          uu____3385 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3379 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3404  ->
                                              match uu____3404 with
                                              | (y,uu____3408) ->
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
                                    let uu____3427 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3427 with
                                     | Some cache_entry ->
                                         let uu____3432 =
                                           let uu____3433 =
                                             let uu____3437 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3437) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3433 in
                                         (uu____3432,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3449 =
                                             let uu____3450 =
                                               let uu____3451 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3451 in
                                             Prims.strcat module_name
                                               uu____3450 in
                                           varops.mk_unique uu____3449 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3460 =
                                             let uu____3464 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3464) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3460 in
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
                                           let uu____3474 =
                                             let uu____3478 =
                                               let uu____3479 =
                                                 let uu____3485 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3485) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3479 in
                                             (uu____3478,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3474 in
                                         let t_kinding =
                                           let uu____3495 =
                                             let uu____3499 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3499,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3495 in
                                         let t_interp =
                                           let uu____3509 =
                                             let uu____3513 =
                                               let uu____3514 =
                                                 let uu____3520 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3520) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3514 in
                                             let uu____3532 =
                                               let uu____3534 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3534 in
                                             (uu____3513, uu____3532,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3509 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3539 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3539);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3560 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3560 in
           let uu____3561 = encode_term_pred None k env ttm in
           (match uu____3561 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3569 =
                    let uu____3573 =
                      let uu____3574 =
                        let uu____3575 =
                          let uu____3576 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3576 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3575 in
                      varops.mk_unique uu____3574 in
                    (t_has_k, (Some "Uvar typing"), uu____3573) in
                  FStar_SMTEncoding_Util.mkAssume uu____3569 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3579 ->
           let uu____3589 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3589 with
            | (head1,args_e) ->
                let uu____3617 =
                  let uu____3625 =
                    let uu____3626 = FStar_Syntax_Subst.compress head1 in
                    uu____3626.FStar_Syntax_Syntax.n in
                  (uu____3625, args_e) in
                (match uu____3617 with
                 | uu____3636 when head_redex env head1 ->
                     let uu____3644 = whnf env t in
                     encode_term uu____3644 env
                 | uu____3645 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____3658;
                       FStar_Syntax_Syntax.pos = uu____3659;
                       FStar_Syntax_Syntax.vars = uu____3660;_},uu____3661),uu____3662::
                    (v1,uu____3664)::(v2,uu____3666)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3704 = encode_term v1 env in
                     (match uu____3704 with
                      | (v11,decls1) ->
                          let uu____3711 = encode_term v2 env in
                          (match uu____3711 with
                           | (v21,decls2) ->
                               let uu____3718 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3718,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3721::(v1,uu____3723)::(v2,uu____3725)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3759 = encode_term v1 env in
                     (match uu____3759 with
                      | (v11,decls1) ->
                          let uu____3766 = encode_term v2 env in
                          (match uu____3766 with
                           | (v21,decls2) ->
                               let uu____3773 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3773,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3775) ->
                     let e0 =
                       let uu____3787 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3787 in
                     ((let uu____3793 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3793
                       then
                         let uu____3794 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3794
                       else ());
                      (let e =
                         let uu____3799 =
                           let uu____3800 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3801 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3800
                             uu____3801 in
                         uu____3799 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3810),(arg,uu____3812)::[]) -> encode_term arg env
                 | uu____3830 ->
                     let uu____3838 = encode_args args_e env in
                     (match uu____3838 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3871 = encode_term head1 env in
                            match uu____3871 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3910 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3910 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3958  ->
                                                 fun uu____3959  ->
                                                   match (uu____3958,
                                                           uu____3959)
                                                   with
                                                   | ((bv,uu____3973),
                                                      (a,uu____3975)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3989 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3989
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3994 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3994 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____4004 =
                                                   let uu____4008 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____4013 =
                                                     let uu____4014 =
                                                       let uu____4015 =
                                                         let uu____4016 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____4016 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____4015 in
                                                     varops.mk_unique
                                                       uu____4014 in
                                                   (uu____4008,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____4013) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____4004 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____4027 = lookup_free_var_sym env fv in
                            match uu____4027 with
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
                                   FStar_Syntax_Syntax.tk = uu____4048;
                                   FStar_Syntax_Syntax.pos = uu____4049;
                                   FStar_Syntax_Syntax.vars = uu____4050;_},uu____4051)
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____4062;
                                   FStar_Syntax_Syntax.pos = uu____4063;
                                   FStar_Syntax_Syntax.vars = uu____4064;_},uu____4065)
                                ->
                                let uu____4070 =
                                  let uu____4071 =
                                    let uu____4074 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4074
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4071
                                    FStar_Pervasives.snd in
                                Some uu____4070
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4090 =
                                  let uu____4091 =
                                    let uu____4094 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4094
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4091
                                    FStar_Pervasives.snd in
                                Some uu____4090
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4109,(FStar_Util.Inl t1,uu____4111),uu____4112)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4150,(FStar_Util.Inr c,uu____4152),uu____4153)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4191 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4211 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4211 in
                               let uu____4212 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4212 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4222;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4223;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4224;_},uu____4225)
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
                                     | uu____4243 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4288 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4288 with
            | (bs1,body1,opening) ->
                let fallback uu____4303 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____4308 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4308, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4319 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____4319
                  | FStar_Util.Inr (eff,uu____4321) ->
                      let uu____4327 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____4327 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4372 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___136_4375 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___136_4375.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___136_4375.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___136_4375.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___136_4375.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___136_4375.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___136_4375.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___136_4375.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___136_4375.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___136_4375.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___136_4375.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___136_4375.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___136_4375.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___136_4375.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___136_4375.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___136_4375.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___136_4375.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___136_4375.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___136_4375.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___136_4375.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___136_4375.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___136_4375.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___136_4375.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___136_4375.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4372 FStar_Syntax_Syntax.U_unknown in
                        let uu____4376 =
                          let uu____4377 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4377 in
                        FStar_Util.Inl uu____4376
                    | FStar_Util.Inr (eff_name,uu____4384) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4415 =
                        let uu____4416 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4416 in
                      FStar_All.pipe_right uu____4415
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4428 =
                        let uu____4429 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4429 FStar_Pervasives.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4437 =
                          let uu____4438 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4438 in
                        FStar_All.pipe_right uu____4437
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4442 =
                             let uu____4443 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4443 in
                           FStar_All.pipe_right uu____4442
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4454 =
                         let uu____4455 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4455 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4454);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4470 =
                       (is_impure lc1) &&
                         (let uu____4472 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4472) in
                     if uu____4470
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4477 = encode_binders None bs1 env in
                        match uu____4477 with
                        | (vars,guards,envbody,decls,uu____4492) ->
                            let uu____4499 =
                              let uu____4507 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4507
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4499 with
                             | (lc2,body2) ->
                                 let uu____4532 = encode_term body2 envbody in
                                 (match uu____4532 with
                                  | (body3,decls') ->
                                      let uu____4539 =
                                        let uu____4544 = codomain_eff lc2 in
                                        match uu____4544 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4556 =
                                              encode_term tfun env in
                                            (match uu____4556 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4539 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4575 =
                                               let uu____4581 =
                                                 let uu____4582 =
                                                   let uu____4585 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4585, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4582 in
                                               ([], vars, uu____4581) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4575 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4593 =
                                                   let uu____4595 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4595 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4593 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4606 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4606 with
                                            | Some cache_entry ->
                                                let uu____4611 =
                                                  let uu____4612 =
                                                    let uu____4616 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4616) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4612 in
                                                (uu____4611,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | None  ->
                                                let uu____4622 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4622 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4629 =
                                                         let uu____4630 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4630 =
                                                           cache_size in
                                                       if uu____4629
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
                                                         let uu____4641 =
                                                           let uu____4642 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4642 in
                                                         varops.mk_unique
                                                           uu____4641 in
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
                                                       let uu____4647 =
                                                         let uu____4651 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4651) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4647 in
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
                                                           let uu____4663 =
                                                             let uu____4664 =
                                                               let uu____4668
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4668,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4664 in
                                                           [uu____4663] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4676 =
                                                         let uu____4680 =
                                                           let uu____4681 =
                                                             let uu____4687 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4687) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4681 in
                                                         (uu____4680,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4676 in
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
                                                     ((let uu____4697 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4697);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4699,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4700;
                          FStar_Syntax_Syntax.lbunivs = uu____4701;
                          FStar_Syntax_Syntax.lbtyp = uu____4702;
                          FStar_Syntax_Syntax.lbeff = uu____4703;
                          FStar_Syntax_Syntax.lbdef = uu____4704;_}::uu____4705),uu____4706)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4724;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4726;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4742 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4755 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4755, [decl_e])))
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
                                  let uu____4916 = encode_pat env1 p in
                                  (match uu____4916 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____4940  ->
                                                   match uu____4940 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____4945 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____4960 =
                                               encode_term w1 env2 in
                                             (match uu____4960 with
                                              | (w2,decls2) ->
                                                  let uu____4968 =
                                                    let uu____4969 =
                                                      let uu____4972 =
                                                        let uu____4973 =
                                                          let uu____4976 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____4976) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____4973 in
                                                      (guard, uu____4972) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____4969 in
                                                  (uu____4968, decls2)) in
                                       (match uu____4945 with
                                        | (guard1,decls2) ->
                                            let uu____4984 =
                                              encode_br br env2 in
                                            (match uu____4984 with
                                             | (br1,decls3) ->
                                                 let uu____4992 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____4992,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4870 with
                      | (match_tm,decls1) ->
                          let uu____5003 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____5003, decls1)))
and encode_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____5025 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5025
       then
         let uu____5026 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5026
       else ());
      (let uu____5028 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5028 with
       | (vars,pat_term) ->
           let uu____5038 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5069  ->
                     fun v1  ->
                       match uu____5069 with
                       | (env1,vars1) ->
                           let uu____5097 = gen_term_var env1 v1 in
                           (match uu____5097 with
                            | (xx,uu____5109,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____5038 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5154 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5155 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5156 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5162 =
                        let uu____5165 = encode_const c in
                        (scrutinee, uu____5165) in
                      FStar_SMTEncoding_Util.mkEq uu____5162
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5178 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5178 with
                        | (uu____5182,uu____5183::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5185 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5206  ->
                                  match uu____5206 with
                                  | (arg,uu____5211) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5215 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5215)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5233) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5252 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5265 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5291  ->
                                  match uu____5291 with
                                  | (arg,uu____5299) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5303 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5303)) in
                      FStar_All.pipe_right uu____5265 FStar_List.flatten in
                let pat_term1 uu____5319 = encode_term pat_term env1 in
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
      let uu____5326 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5350  ->
                fun uu____5351  ->
                  match (uu____5350, uu____5351) with
                  | ((tms,decls),(t,uu____5371)) ->
                      let uu____5382 = encode_term t env in
                      (match uu____5382 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5326 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5416 = FStar_Syntax_Util.list_elements e in
        match uu____5416 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5431 =
          let uu____5441 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5441 FStar_Syntax_Util.head_and_args in
        match uu____5431 with
        | (head1,args) ->
            let uu____5469 =
              let uu____5477 =
                let uu____5478 = FStar_Syntax_Util.un_uinst head1 in
                uu____5478.FStar_Syntax_Syntax.n in
              (uu____5477, args) in
            (match uu____5469 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5489,uu____5490)::(e,uu____5492)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> e
             | uu____5518 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____5545 =
            let uu____5555 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5555 FStar_Syntax_Util.head_and_args in
          match uu____5545 with
          | (head1,args) ->
              let uu____5584 =
                let uu____5592 =
                  let uu____5593 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5593.FStar_Syntax_Syntax.n in
                (uu____5592, args) in
              (match uu____5584 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5606)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5626 -> None) in
        match elts with
        | t1::[] ->
            let uu____5641 = smt_pat_or1 t1 in
            (match uu____5641 with
             | Some e ->
                 let uu____5654 = list_elements1 e in
                 FStar_All.pipe_right uu____5654
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5667 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5667
                           (FStar_List.map one_pat)))
             | uu____5675 ->
                 let uu____5679 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5679])
        | uu____5695 ->
            let uu____5697 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5697] in
      let uu____5713 =
        let uu____5726 =
          let uu____5727 = FStar_Syntax_Subst.compress t in
          uu____5727.FStar_Syntax_Syntax.n in
        match uu____5726 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5754 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5754 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5783;
                        FStar_Syntax_Syntax.effect_name = uu____5784;
                        FStar_Syntax_Syntax.result_typ = uu____5785;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5787)::(post,uu____5789)::(pats,uu____5791)::[];
                        FStar_Syntax_Syntax.flags = uu____5792;_}
                      ->
                      let uu____5824 = lemma_pats pats in
                      (binders1, pre, post, uu____5824)
                  | uu____5837 -> failwith "impos"))
        | uu____5850 -> failwith "Impos" in
      match uu____5713 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___137_5886 = env in
            {
              bindings = (uu___137_5886.bindings);
              depth = (uu___137_5886.depth);
              tcenv = (uu___137_5886.tcenv);
              warn = (uu___137_5886.warn);
              cache = (uu___137_5886.cache);
              nolabels = (uu___137_5886.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___137_5886.encode_non_total_function_typ);
              current_module_name = (uu___137_5886.current_module_name)
            } in
          let uu____5887 = encode_binders None binders env1 in
          (match uu____5887 with
           | (vars,guards,env2,decls,uu____5902) ->
               let uu____5909 =
                 let uu____5916 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____5942 =
                             let uu____5947 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____5947 FStar_List.unzip in
                           match uu____5942 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____5916 FStar_List.unzip in
               (match uu____5909 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___138_6006 = env2 in
                      {
                        bindings = (uu___138_6006.bindings);
                        depth = (uu___138_6006.depth);
                        tcenv = (uu___138_6006.tcenv);
                        warn = (uu___138_6006.warn);
                        cache = (uu___138_6006.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___138_6006.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___138_6006.encode_non_total_function_typ);
                        current_module_name =
                          (uu___138_6006.current_module_name)
                      } in
                    let uu____6007 =
                      let uu____6010 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6010 env3 in
                    (match uu____6007 with
                     | (pre1,decls'') ->
                         let uu____6015 =
                           let uu____6018 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6018 env3 in
                         (match uu____6015 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6025 =
                                let uu____6026 =
                                  let uu____6032 =
                                    let uu____6033 =
                                      let uu____6036 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6036, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6033 in
                                  (pats, vars, uu____6032) in
                                FStar_SMTEncoding_Util.mkForall uu____6026 in
                              (uu____6025, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6049 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6049
        then
          let uu____6050 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6051 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6050 uu____6051
        else () in
      let enc f r l =
        let uu____6078 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6096 = encode_term (fst x) env in
                 match uu____6096 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6078 with
        | (decls,args) ->
            let uu____6113 =
              let uu___139_6114 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6114.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6114.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6113, decls) in
      let const_op f r uu____6133 = let uu____6136 = f r in (uu____6136, []) in
      let un_op f l =
        let uu____6152 = FStar_List.hd l in FStar_All.pipe_left f uu____6152 in
      let bin_op f uu___111_6165 =
        match uu___111_6165 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6173 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6200 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6216  ->
                 match uu____6216 with
                 | (t,uu____6224) ->
                     let uu____6225 = encode_formula t env in
                     (match uu____6225 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6200 with
        | (decls,phis) ->
            let uu____6242 =
              let uu___140_6243 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_6243.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_6243.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6242, decls) in
      let eq_op r uu___112_6259 =
        match uu___112_6259 with
        | uu____6262::e1::e2::[] ->
            let uu____6293 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6293 r [e1; e2]
        | uu____6312::uu____6313::e1::e2::[] ->
            let uu____6352 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6352 r [e1; e2]
        | l ->
            let uu____6372 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6372 r l in
      let mk_imp1 r uu___113_6391 =
        match uu___113_6391 with
        | (lhs,uu____6395)::(rhs,uu____6397)::[] ->
            let uu____6418 = encode_formula rhs env in
            (match uu____6418 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6427) ->
                      (l1, decls1)
                  | uu____6430 ->
                      let uu____6431 = encode_formula lhs env in
                      (match uu____6431 with
                       | (l2,decls2) ->
                           let uu____6438 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6438, (FStar_List.append decls1 decls2)))))
        | uu____6440 -> failwith "impossible" in
      let mk_ite r uu___114_6455 =
        match uu___114_6455 with
        | (guard,uu____6459)::(_then,uu____6461)::(_else,uu____6463)::[] ->
            let uu____6492 = encode_formula guard env in
            (match uu____6492 with
             | (g,decls1) ->
                 let uu____6499 = encode_formula _then env in
                 (match uu____6499 with
                  | (t,decls2) ->
                      let uu____6506 = encode_formula _else env in
                      (match uu____6506 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6515 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6534 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6534 in
      let connectives =
        let uu____6546 =
          let uu____6555 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6555) in
        let uu____6568 =
          let uu____6578 =
            let uu____6587 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6587) in
          let uu____6600 =
            let uu____6610 =
              let uu____6620 =
                let uu____6629 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6629) in
              let uu____6642 =
                let uu____6652 =
                  let uu____6662 =
                    let uu____6671 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6671) in
                  [uu____6662;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6652 in
              uu____6620 :: uu____6642 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6610 in
          uu____6578 :: uu____6600 in
        uu____6546 :: uu____6568 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6833 = encode_formula phi' env in
            (match uu____6833 with
             | (phi2,decls) ->
                 let uu____6840 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6840, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6841 ->
            let uu____6846 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6846 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6873 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6873 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6881;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6883;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6899 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6899 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6931::(x,uu____6933)::(t,uu____6935)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6969 = encode_term x env in
                 (match uu____6969 with
                  | (x1,decls) ->
                      let uu____6976 = encode_term t env in
                      (match uu____6976 with
                       | (t1,decls') ->
                           let uu____6983 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6983, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6987)::(msg,uu____6989)::(phi2,uu____6991)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____7025 =
                   let uu____7028 =
                     let uu____7029 = FStar_Syntax_Subst.compress r in
                     uu____7029.FStar_Syntax_Syntax.n in
                   let uu____7032 =
                     let uu____7033 = FStar_Syntax_Subst.compress msg in
                     uu____7033.FStar_Syntax_Syntax.n in
                   (uu____7028, uu____7032) in
                 (match uu____7025 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7040))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  ((FStar_Util.string_of_unicode s), r1,
                                    false)))) None r1 in
                      fallback phi3
                  | uu____7052 -> fallback phi2)
             | uu____7055 when head_redex env head2 ->
                 let uu____7063 = whnf env phi1 in
                 encode_formula uu____7063 env
             | uu____7064 ->
                 let uu____7072 = encode_term phi1 env in
                 (match uu____7072 with
                  | (tt,decls) ->
                      let uu____7079 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___141_7082 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___141_7082.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___141_7082.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7079, decls)))
        | uu____7085 ->
            let uu____7086 = encode_term phi1 env in
            (match uu____7086 with
             | (tt,decls) ->
                 let uu____7093 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___142_7096 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___142_7096.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___142_7096.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7093, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7123 = encode_binders None bs env1 in
        match uu____7123 with
        | (vars,guards,env2,decls,uu____7145) ->
            let uu____7152 =
              let uu____7159 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7186 =
                          let uu____7191 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7208  ->
                                    match uu____7208 with
                                    | (t,uu____7214) ->
                                        encode_term t
                                          (let uu___143_7216 = env2 in
                                           {
                                             bindings =
                                               (uu___143_7216.bindings);
                                             depth = (uu___143_7216.depth);
                                             tcenv = (uu___143_7216.tcenv);
                                             warn = (uu___143_7216.warn);
                                             cache = (uu___143_7216.cache);
                                             nolabels =
                                               (uu___143_7216.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___143_7216.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___143_7216.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7191 FStar_List.unzip in
                        match uu____7186 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7159 FStar_List.unzip in
            (match uu____7152 with
             | (pats,decls') ->
                 let uu____7268 = encode_formula body env2 in
                 (match uu____7268 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7287;
                             FStar_SMTEncoding_Term.rng = uu____7288;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7296 -> guards in
                      let uu____7299 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7299, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7336  ->
                   match uu____7336 with
                   | (x,uu____7340) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7346 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7355 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7355) uu____7346 tl1 in
             let uu____7357 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7373  ->
                       match uu____7373 with
                       | (b,uu____7377) ->
                           let uu____7378 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7378)) in
             (match uu____7357 with
              | None  -> ()
              | Some (x,uu____7382) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7394 =
                    let uu____7395 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7395 in
                  FStar_Errors.warn pos uu____7394) in
       let uu____7396 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7396 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7402 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7441  ->
                     match uu____7441 with
                     | (l,uu____7451) -> FStar_Ident.lid_equals op l)) in
           (match uu____7402 with
            | None  -> fallback phi1
            | Some (uu____7474,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7503 = encode_q_body env vars pats body in
             match uu____7503 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7529 =
                     let uu____7535 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7535) in
                   FStar_SMTEncoding_Term.mkForall uu____7529
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7547 = encode_q_body env vars pats body in
             match uu____7547 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7572 =
                   let uu____7573 =
                     let uu____7579 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7579) in
                   FStar_SMTEncoding_Term.mkExists uu____7573
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7572, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7633 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7633 with
  | (asym,a) ->
      let uu____7638 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7638 with
       | (xsym,x) ->
           let uu____7643 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7643 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7673 =
                      let uu____7679 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____7679, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7673 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7694 =
                      let uu____7698 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7698) in
                    FStar_SMTEncoding_Util.mkApp uu____7694 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7706 =
                    let uu____7708 =
                      let uu____7710 =
                        let uu____7712 =
                          let uu____7713 =
                            let uu____7717 =
                              let uu____7718 =
                                let uu____7724 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7724) in
                              FStar_SMTEncoding_Util.mkForall uu____7718 in
                            (uu____7717, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7713 in
                        let uu____7733 =
                          let uu____7735 =
                            let uu____7736 =
                              let uu____7740 =
                                let uu____7741 =
                                  let uu____7747 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7747) in
                                FStar_SMTEncoding_Util.mkForall uu____7741 in
                              (uu____7740,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7736 in
                          [uu____7735] in
                        uu____7712 :: uu____7733 in
                      xtok_decl :: uu____7710 in
                    xname_decl :: uu____7708 in
                  (xtok1, uu____7706) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7796 =
                    let uu____7804 =
                      let uu____7810 =
                        let uu____7811 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7811 in
                      quant axy uu____7810 in
                    (FStar_Syntax_Const.op_Eq, uu____7804) in
                  let uu____7817 =
                    let uu____7826 =
                      let uu____7834 =
                        let uu____7840 =
                          let uu____7841 =
                            let uu____7842 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7842 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7841 in
                        quant axy uu____7840 in
                      (FStar_Syntax_Const.op_notEq, uu____7834) in
                    let uu____7848 =
                      let uu____7857 =
                        let uu____7865 =
                          let uu____7871 =
                            let uu____7872 =
                              let uu____7873 =
                                let uu____7876 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7877 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7876, uu____7877) in
                              FStar_SMTEncoding_Util.mkLT uu____7873 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7872 in
                          quant xy uu____7871 in
                        (FStar_Syntax_Const.op_LT, uu____7865) in
                      let uu____7883 =
                        let uu____7892 =
                          let uu____7900 =
                            let uu____7906 =
                              let uu____7907 =
                                let uu____7908 =
                                  let uu____7911 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7912 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7911, uu____7912) in
                                FStar_SMTEncoding_Util.mkLTE uu____7908 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7907 in
                            quant xy uu____7906 in
                          (FStar_Syntax_Const.op_LTE, uu____7900) in
                        let uu____7918 =
                          let uu____7927 =
                            let uu____7935 =
                              let uu____7941 =
                                let uu____7942 =
                                  let uu____7943 =
                                    let uu____7946 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7947 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7946, uu____7947) in
                                  FStar_SMTEncoding_Util.mkGT uu____7943 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7942 in
                              quant xy uu____7941 in
                            (FStar_Syntax_Const.op_GT, uu____7935) in
                          let uu____7953 =
                            let uu____7962 =
                              let uu____7970 =
                                let uu____7976 =
                                  let uu____7977 =
                                    let uu____7978 =
                                      let uu____7981 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7982 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7981, uu____7982) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7978 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7977 in
                                quant xy uu____7976 in
                              (FStar_Syntax_Const.op_GTE, uu____7970) in
                            let uu____7988 =
                              let uu____7997 =
                                let uu____8005 =
                                  let uu____8011 =
                                    let uu____8012 =
                                      let uu____8013 =
                                        let uu____8016 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____8017 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____8016, uu____8017) in
                                      FStar_SMTEncoding_Util.mkSub uu____8013 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8012 in
                                  quant xy uu____8011 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____8005) in
                              let uu____8023 =
                                let uu____8032 =
                                  let uu____8040 =
                                    let uu____8046 =
                                      let uu____8047 =
                                        let uu____8048 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8048 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8047 in
                                    quant qx uu____8046 in
                                  (FStar_Syntax_Const.op_Minus, uu____8040) in
                                let uu____8054 =
                                  let uu____8063 =
                                    let uu____8071 =
                                      let uu____8077 =
                                        let uu____8078 =
                                          let uu____8079 =
                                            let uu____8082 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8083 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8082, uu____8083) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8079 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8078 in
                                      quant xy uu____8077 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8071) in
                                  let uu____8089 =
                                    let uu____8098 =
                                      let uu____8106 =
                                        let uu____8112 =
                                          let uu____8113 =
                                            let uu____8114 =
                                              let uu____8117 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8118 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8117, uu____8118) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8114 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8113 in
                                        quant xy uu____8112 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8106) in
                                    let uu____8124 =
                                      let uu____8133 =
                                        let uu____8141 =
                                          let uu____8147 =
                                            let uu____8148 =
                                              let uu____8149 =
                                                let uu____8152 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8153 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8152, uu____8153) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8149 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8148 in
                                          quant xy uu____8147 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8141) in
                                      let uu____8159 =
                                        let uu____8168 =
                                          let uu____8176 =
                                            let uu____8182 =
                                              let uu____8183 =
                                                let uu____8184 =
                                                  let uu____8187 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8188 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8187, uu____8188) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8184 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8183 in
                                            quant xy uu____8182 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8176) in
                                        let uu____8194 =
                                          let uu____8203 =
                                            let uu____8211 =
                                              let uu____8217 =
                                                let uu____8218 =
                                                  let uu____8219 =
                                                    let uu____8222 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8223 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8222, uu____8223) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8219 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8218 in
                                              quant xy uu____8217 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8211) in
                                          let uu____8229 =
                                            let uu____8238 =
                                              let uu____8246 =
                                                let uu____8252 =
                                                  let uu____8253 =
                                                    let uu____8254 =
                                                      let uu____8257 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8258 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8257,
                                                        uu____8258) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8254 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8253 in
                                                quant xy uu____8252 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8246) in
                                            let uu____8264 =
                                              let uu____8273 =
                                                let uu____8281 =
                                                  let uu____8287 =
                                                    let uu____8288 =
                                                      let uu____8289 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8289 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8288 in
                                                  quant qx uu____8287 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8281) in
                                              [uu____8273] in
                                            uu____8238 :: uu____8264 in
                                          uu____8203 :: uu____8229 in
                                        uu____8168 :: uu____8194 in
                                      uu____8133 :: uu____8159 in
                                    uu____8098 :: uu____8124 in
                                  uu____8063 :: uu____8089 in
                                uu____8032 :: uu____8054 in
                              uu____7997 :: uu____8023 in
                            uu____7962 :: uu____7988 in
                          uu____7927 :: uu____7953 in
                        uu____7892 :: uu____7918 in
                      uu____7857 :: uu____7883 in
                    uu____7826 :: uu____7848 in
                  uu____7796 :: uu____7817 in
                let mk1 l v1 =
                  let uu____8417 =
                    let uu____8422 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8457  ->
                              match uu____8457 with
                              | (l',uu____8466) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8422
                      (FStar_Option.map
                         (fun uu____8502  ->
                            match uu____8502 with | (uu____8513,b) -> b v1)) in
                  FStar_All.pipe_right uu____8417 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8557  ->
                          match uu____8557 with
                          | (l',uu____8566) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8592 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8592 with
        | (xxsym,xx) ->
            let uu____8597 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8597 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8605 =
                   let uu____8609 =
                     let uu____8610 =
                       let uu____8616 =
                         let uu____8617 =
                           let uu____8620 =
                             let uu____8621 =
                               let uu____8624 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8624) in
                             FStar_SMTEncoding_Util.mkEq uu____8621 in
                           (xx_has_type, uu____8620) in
                         FStar_SMTEncoding_Util.mkImp uu____8617 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8616) in
                     FStar_SMTEncoding_Util.mkForall uu____8610 in
                   let uu____8637 =
                     let uu____8638 =
                       let uu____8639 =
                         let uu____8640 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8640 in
                       Prims.strcat module_name uu____8639 in
                     varops.mk_unique uu____8638 in
                   (uu____8609, (Some "pretyping"), uu____8637) in
                 FStar_SMTEncoding_Util.mkAssume uu____8605)
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
    let uu____8670 =
      let uu____8671 =
        let uu____8675 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8675, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8671 in
    let uu____8677 =
      let uu____8679 =
        let uu____8680 =
          let uu____8684 =
            let uu____8685 =
              let uu____8691 =
                let uu____8692 =
                  let uu____8695 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8695) in
                FStar_SMTEncoding_Util.mkImp uu____8692 in
              ([[typing_pred]], [xx], uu____8691) in
            mkForall_fuel uu____8685 in
          (uu____8684, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8680 in
      [uu____8679] in
    uu____8670 :: uu____8677 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8723 =
      let uu____8724 =
        let uu____8728 =
          let uu____8729 =
            let uu____8735 =
              let uu____8738 =
                let uu____8740 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8740] in
              [uu____8738] in
            let uu____8743 =
              let uu____8744 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8744 tt in
            (uu____8735, [bb], uu____8743) in
          FStar_SMTEncoding_Util.mkForall uu____8729 in
        (uu____8728, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8724 in
    let uu____8755 =
      let uu____8757 =
        let uu____8758 =
          let uu____8762 =
            let uu____8763 =
              let uu____8769 =
                let uu____8770 =
                  let uu____8773 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8773) in
                FStar_SMTEncoding_Util.mkImp uu____8770 in
              ([[typing_pred]], [xx], uu____8769) in
            mkForall_fuel uu____8763 in
          (uu____8762, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8758 in
      [uu____8757] in
    uu____8723 :: uu____8755 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8807 =
        let uu____8808 =
          let uu____8812 =
            let uu____8814 =
              let uu____8816 =
                let uu____8818 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8819 =
                  let uu____8821 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8821] in
                uu____8818 :: uu____8819 in
              tt :: uu____8816 in
            tt :: uu____8814 in
          ("Prims.Precedes", uu____8812) in
        FStar_SMTEncoding_Util.mkApp uu____8808 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8807 in
    let precedes_y_x =
      let uu____8824 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8824 in
    let uu____8826 =
      let uu____8827 =
        let uu____8831 =
          let uu____8832 =
            let uu____8838 =
              let uu____8841 =
                let uu____8843 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8843] in
              [uu____8841] in
            let uu____8846 =
              let uu____8847 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8847 tt in
            (uu____8838, [bb], uu____8846) in
          FStar_SMTEncoding_Util.mkForall uu____8832 in
        (uu____8831, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8827 in
    let uu____8858 =
      let uu____8860 =
        let uu____8861 =
          let uu____8865 =
            let uu____8866 =
              let uu____8872 =
                let uu____8873 =
                  let uu____8876 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8876) in
                FStar_SMTEncoding_Util.mkImp uu____8873 in
              ([[typing_pred]], [xx], uu____8872) in
            mkForall_fuel uu____8866 in
          (uu____8865, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8861 in
      let uu____8889 =
        let uu____8891 =
          let uu____8892 =
            let uu____8896 =
              let uu____8897 =
                let uu____8903 =
                  let uu____8904 =
                    let uu____8907 =
                      let uu____8908 =
                        let uu____8910 =
                          let uu____8912 =
                            let uu____8914 =
                              let uu____8915 =
                                let uu____8918 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8919 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8918, uu____8919) in
                              FStar_SMTEncoding_Util.mkGT uu____8915 in
                            let uu____8920 =
                              let uu____8922 =
                                let uu____8923 =
                                  let uu____8926 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8927 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8926, uu____8927) in
                                FStar_SMTEncoding_Util.mkGTE uu____8923 in
                              let uu____8928 =
                                let uu____8930 =
                                  let uu____8931 =
                                    let uu____8934 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8935 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8934, uu____8935) in
                                  FStar_SMTEncoding_Util.mkLT uu____8931 in
                                [uu____8930] in
                              uu____8922 :: uu____8928 in
                            uu____8914 :: uu____8920 in
                          typing_pred_y :: uu____8912 in
                        typing_pred :: uu____8910 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8908 in
                    (uu____8907, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8904 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8903) in
              mkForall_fuel uu____8897 in
            (uu____8896, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8892 in
        [uu____8891] in
      uu____8860 :: uu____8889 in
    uu____8826 :: uu____8858 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8965 =
      let uu____8966 =
        let uu____8970 =
          let uu____8971 =
            let uu____8977 =
              let uu____8980 =
                let uu____8982 = FStar_SMTEncoding_Term.boxString b in
                [uu____8982] in
              [uu____8980] in
            let uu____8985 =
              let uu____8986 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8986 tt in
            (uu____8977, [bb], uu____8985) in
          FStar_SMTEncoding_Util.mkForall uu____8971 in
        (uu____8970, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8966 in
    let uu____8997 =
      let uu____8999 =
        let uu____9000 =
          let uu____9004 =
            let uu____9005 =
              let uu____9011 =
                let uu____9012 =
                  let uu____9015 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____9015) in
                FStar_SMTEncoding_Util.mkImp uu____9012 in
              ([[typing_pred]], [xx], uu____9011) in
            mkForall_fuel uu____9005 in
          (uu____9004, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9000 in
      [uu____8999] in
    uu____8965 :: uu____8997 in
  let mk_ref1 env reft_name uu____9037 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____9048 =
        let uu____9052 =
          let uu____9054 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9054] in
        (reft_name, uu____9052) in
      FStar_SMTEncoding_Util.mkApp uu____9048 in
    let refb =
      let uu____9057 =
        let uu____9061 =
          let uu____9063 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9063] in
        (reft_name, uu____9061) in
      FStar_SMTEncoding_Util.mkApp uu____9057 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9067 =
      let uu____9068 =
        let uu____9072 =
          let uu____9073 =
            let uu____9079 =
              let uu____9080 =
                let uu____9083 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9083) in
              FStar_SMTEncoding_Util.mkImp uu____9080 in
            ([[typing_pred]], [xx; aa], uu____9079) in
          mkForall_fuel uu____9073 in
        (uu____9072, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9068 in
    [uu____9067] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9123 =
      let uu____9124 =
        let uu____9128 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9128, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9124 in
    [uu____9123] in
  let mk_and_interp env conj uu____9139 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9156 =
      let uu____9157 =
        let uu____9161 =
          let uu____9162 =
            let uu____9168 =
              let uu____9169 =
                let uu____9172 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9172, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9169 in
            ([[l_and_a_b]], [aa; bb], uu____9168) in
          FStar_SMTEncoding_Util.mkForall uu____9162 in
        (uu____9161, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9157 in
    [uu____9156] in
  let mk_or_interp env disj uu____9196 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9213 =
      let uu____9214 =
        let uu____9218 =
          let uu____9219 =
            let uu____9225 =
              let uu____9226 =
                let uu____9229 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9229, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9226 in
            ([[l_or_a_b]], [aa; bb], uu____9225) in
          FStar_SMTEncoding_Util.mkForall uu____9219 in
        (uu____9218, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9214 in
    [uu____9213] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9270 =
      let uu____9271 =
        let uu____9275 =
          let uu____9276 =
            let uu____9282 =
              let uu____9283 =
                let uu____9286 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9286, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9283 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9282) in
          FStar_SMTEncoding_Util.mkForall uu____9276 in
        (uu____9275, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9271 in
    [uu____9270] in
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
    let uu____9333 =
      let uu____9334 =
        let uu____9338 =
          let uu____9339 =
            let uu____9345 =
              let uu____9346 =
                let uu____9349 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9349, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9346 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9345) in
          FStar_SMTEncoding_Util.mkForall uu____9339 in
        (uu____9338, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9334 in
    [uu____9333] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9394 =
      let uu____9395 =
        let uu____9399 =
          let uu____9400 =
            let uu____9406 =
              let uu____9407 =
                let uu____9410 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9410, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9407 in
            ([[l_imp_a_b]], [aa; bb], uu____9406) in
          FStar_SMTEncoding_Util.mkForall uu____9400 in
        (uu____9399, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9395 in
    [uu____9394] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9451 =
      let uu____9452 =
        let uu____9456 =
          let uu____9457 =
            let uu____9463 =
              let uu____9464 =
                let uu____9467 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9467, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9464 in
            ([[l_iff_a_b]], [aa; bb], uu____9463) in
          FStar_SMTEncoding_Util.mkForall uu____9457 in
        (uu____9456, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9452 in
    [uu____9451] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9501 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9501 in
    let uu____9503 =
      let uu____9504 =
        let uu____9508 =
          let uu____9509 =
            let uu____9515 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9515) in
          FStar_SMTEncoding_Util.mkForall uu____9509 in
        (uu____9508, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9504 in
    [uu____9503] in
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
      let uu____9555 =
        let uu____9559 =
          let uu____9561 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9561] in
        ("Valid", uu____9559) in
      FStar_SMTEncoding_Util.mkApp uu____9555 in
    let uu____9563 =
      let uu____9564 =
        let uu____9568 =
          let uu____9569 =
            let uu____9575 =
              let uu____9576 =
                let uu____9579 =
                  let uu____9580 =
                    let uu____9586 =
                      let uu____9589 =
                        let uu____9591 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9591] in
                      [uu____9589] in
                    let uu____9594 =
                      let uu____9595 =
                        let uu____9598 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9598, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9595 in
                    (uu____9586, [xx1], uu____9594) in
                  FStar_SMTEncoding_Util.mkForall uu____9580 in
                (uu____9579, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9576 in
            ([[l_forall_a_b]], [aa; bb], uu____9575) in
          FStar_SMTEncoding_Util.mkForall uu____9569 in
        (uu____9568, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9564 in
    [uu____9563] in
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
      let uu____9649 =
        let uu____9653 =
          let uu____9655 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9655] in
        ("Valid", uu____9653) in
      FStar_SMTEncoding_Util.mkApp uu____9649 in
    let uu____9657 =
      let uu____9658 =
        let uu____9662 =
          let uu____9663 =
            let uu____9669 =
              let uu____9670 =
                let uu____9673 =
                  let uu____9674 =
                    let uu____9680 =
                      let uu____9683 =
                        let uu____9685 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9685] in
                      [uu____9683] in
                    let uu____9688 =
                      let uu____9689 =
                        let uu____9692 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9692, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9689 in
                    (uu____9680, [xx1], uu____9688) in
                  FStar_SMTEncoding_Util.mkExists uu____9674 in
                (uu____9673, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9670 in
            ([[l_exists_a_b]], [aa; bb], uu____9669) in
          FStar_SMTEncoding_Util.mkForall uu____9663 in
        (uu____9662, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9658 in
    [uu____9657] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9728 =
      let uu____9729 =
        let uu____9733 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9734 = varops.mk_unique "typing_range_const" in
        (uu____9733, (Some "Range_const typing"), uu____9734) in
      FStar_SMTEncoding_Util.mkAssume uu____9729 in
    [uu____9728] in
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
          let uu____9996 =
            FStar_Util.find_opt
              (fun uu____10017  ->
                 match uu____10017 with
                 | (l,uu____10027) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9996 with
          | None  -> []
          | Some (uu____10049,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10082 = encode_function_type_as_formula t env in
        match uu____10082 with
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
            let uu____10110 =
              (let uu____10113 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10113) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10110
            then
              let uu____10117 = new_term_constant_and_tok_from_lid env lid in
              match uu____10117 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10129 =
                      let uu____10130 = FStar_Syntax_Subst.compress t_norm in
                      uu____10130.FStar_Syntax_Syntax.n in
                    match uu____10129 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10135) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10153  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10156 -> [] in
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
              (let uu____10165 = prims.is lid in
               if uu____10165
               then
                 let vname = varops.new_fvar lid in
                 let uu____10170 = prims.mk lid vname in
                 match uu____10170 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10185 =
                    let uu____10191 = curried_arrow_formals_comp t_norm in
                    match uu____10191 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10202 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10202
                          then
                            let uu____10203 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___144_10206 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___144_10206.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___144_10206.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___144_10206.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___144_10206.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___144_10206.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___144_10206.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___144_10206.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___144_10206.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___144_10206.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___144_10206.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___144_10206.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___144_10206.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___144_10206.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___144_10206.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___144_10206.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___144_10206.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___144_10206.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___144_10206.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___144_10206.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___144_10206.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___144_10206.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___144_10206.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___144_10206.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10203
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10213 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10213)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10185 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10240 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10240 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10253 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10285  ->
                                     match uu___115_10285 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10288 =
                                           FStar_Util.prefix vars in
                                         (match uu____10288 with
                                          | (uu____10299,(xxsym,uu____10301))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10311 =
                                                let uu____10312 =
                                                  let uu____10316 =
                                                    let uu____10317 =
                                                      let uu____10323 =
                                                        let uu____10324 =
                                                          let uu____10327 =
                                                            let uu____10328 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10328 in
                                                          (vapp, uu____10327) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10324 in
                                                      ([[vapp]], vars,
                                                        uu____10323) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10317 in
                                                  (uu____10316,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10312 in
                                              [uu____10311])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10339 =
                                           FStar_Util.prefix vars in
                                         (match uu____10339 with
                                          | (uu____10350,(xxsym,uu____10352))
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
                                              let uu____10366 =
                                                let uu____10367 =
                                                  let uu____10371 =
                                                    let uu____10372 =
                                                      let uu____10378 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10378) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10372 in
                                                  (uu____10371,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10367 in
                                              [uu____10366])
                                     | uu____10387 -> [])) in
                           let uu____10388 = encode_binders None formals env1 in
                           (match uu____10388 with
                            | (vars,guards,env',decls1,uu____10404) ->
                                let uu____10411 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10416 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10416, decls1)
                                  | Some p ->
                                      let uu____10418 = encode_formula p env' in
                                      (match uu____10418 with
                                       | (g,ds) ->
                                           let uu____10425 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10425,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10411 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10434 =
                                         let uu____10438 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10438) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10434 in
                                     let uu____10443 =
                                       let vname_decl =
                                         let uu____10448 =
                                           let uu____10454 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10460  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10454,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10448 in
                                       let uu____10465 =
                                         let env2 =
                                           let uu___145_10469 = env1 in
                                           {
                                             bindings =
                                               (uu___145_10469.bindings);
                                             depth = (uu___145_10469.depth);
                                             tcenv = (uu___145_10469.tcenv);
                                             warn = (uu___145_10469.warn);
                                             cache = (uu___145_10469.cache);
                                             nolabels =
                                               (uu___145_10469.nolabels);
                                             use_zfuel_name =
                                               (uu___145_10469.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___145_10469.current_module_name)
                                           } in
                                         let uu____10470 =
                                           let uu____10471 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10471 in
                                         if uu____10470
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10465 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10481::uu____10482 ->
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
                                                   let uu____10505 =
                                                     let uu____10511 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10511) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10505 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10525 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10527 =
                                             match formals with
                                             | [] ->
                                                 let uu____10536 =
                                                   let uu____10537 =
                                                     let uu____10539 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10539 in
                                                   push_free_var env1 lid
                                                     vname uu____10537 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10536)
                                             | uu____10542 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10547 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10547 in
                                                 let name_tok_corr =
                                                   let uu____10549 =
                                                     let uu____10553 =
                                                       let uu____10554 =
                                                         let uu____10560 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10560) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10554 in
                                                     (uu____10553,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10549 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10527 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10443 with
                                      | (decls2,env2) ->
                                          let uu____10584 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10589 =
                                              encode_term res_t1 env' in
                                            match uu____10589 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10597 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10597,
                                                  decls) in
                                          (match uu____10584 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10605 =
                                                   let uu____10609 =
                                                     let uu____10610 =
                                                       let uu____10616 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10616) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10610 in
                                                   (uu____10609,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10605 in
                                               let freshness =
                                                 let uu____10625 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10625
                                                 then
                                                   let uu____10628 =
                                                     let uu____10629 =
                                                       let uu____10635 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
                                                       let uu____10641 =
                                                         varops.next_id () in
                                                       (vname, uu____10635,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10641) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10629 in
                                                   let uu____10643 =
                                                     let uu____10645 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10645] in
                                                   uu____10628 :: uu____10643
                                                 else [] in
                                               let g =
                                                 let uu____10649 =
                                                   let uu____10651 =
                                                     let uu____10653 =
                                                       let uu____10655 =
                                                         let uu____10657 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10657 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10655 in
                                                     FStar_List.append decls3
                                                       uu____10653 in
                                                   FStar_List.append decls2
                                                     uu____10651 in
                                                 FStar_List.append decls11
                                                   uu____10649 in
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
          let uu____10679 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10679 with
          | None  ->
              let uu____10698 = encode_free_var env x t t_norm [] in
              (match uu____10698 with
               | (decls,env1) ->
                   let uu____10713 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10713 with
                    | (n1,x',uu____10728) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10740) -> ((n1, x1), [], env)
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
          let uu____10773 = encode_free_var env lid t tt quals in
          match uu____10773 with
          | (decls,env1) ->
              let uu____10784 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10784
              then
                let uu____10788 =
                  let uu____10790 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10790 in
                (uu____10788, env1)
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
             (fun uu____10825  ->
                fun lb  ->
                  match uu____10825 with
                  | (decls,env1) ->
                      let uu____10837 =
                        let uu____10841 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10841
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10837 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10855 = FStar_Syntax_Util.head_and_args t in
    match uu____10855 with
    | (hd1,args) ->
        let uu____10881 =
          let uu____10882 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10882.FStar_Syntax_Syntax.n in
        (match uu____10881 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10886,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10899 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10914  ->
      fun quals  ->
        match uu____10914 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10963 = FStar_Util.first_N nbinders formals in
              match uu____10963 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11010  ->
                         fun uu____11011  ->
                           match (uu____11010, uu____11011) with
                           | ((formal,uu____11021),(binder,uu____11023)) ->
                               let uu____11028 =
                                 let uu____11033 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11033) in
                               FStar_Syntax_Syntax.NT uu____11028) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11038 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11056  ->
                              match uu____11056 with
                              | (x,i) ->
                                  let uu____11063 =
                                    let uu___146_11064 = x in
                                    let uu____11065 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___146_11064.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___146_11064.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11065
                                    } in
                                  (uu____11063, i))) in
                    FStar_All.pipe_right uu____11038
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11077 =
                      let uu____11079 =
                        let uu____11080 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11080.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____11079 in
                    let uu____11084 =
                      let uu____11085 = FStar_Syntax_Subst.compress body in
                      let uu____11086 =
                        let uu____11087 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11087 in
                      FStar_Syntax_Syntax.extend_app_n uu____11085
                        uu____11086 in
                    uu____11084 uu____11077 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11129 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11129
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___147_11132 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___147_11132.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___147_11132.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___147_11132.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___147_11132.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___147_11132.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___147_11132.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___147_11132.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___147_11132.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___147_11132.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___147_11132.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___147_11132.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___147_11132.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___147_11132.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___147_11132.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___147_11132.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___147_11132.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___147_11132.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___147_11132.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___147_11132.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___147_11132.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___147_11132.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___147_11132.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___147_11132.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11153 = FStar_Syntax_Util.abs_formals e in
                match uu____11153 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11202::uu____11203 ->
                         let uu____11211 =
                           let uu____11212 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11212.FStar_Syntax_Syntax.n in
                         (match uu____11211 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11239 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11239 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11265 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11265
                                   then
                                     let uu____11283 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11283 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11336  ->
                                                   fun uu____11337  ->
                                                     match (uu____11336,
                                                             uu____11337)
                                                     with
                                                     | ((x,uu____11347),
                                                        (b,uu____11349)) ->
                                                         let uu____11354 =
                                                           let uu____11359 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11359) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11354)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11361 =
                                            let uu____11372 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11372) in
                                          (uu____11361, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11407 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11407 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11459) ->
                              let uu____11464 =
                                let uu____11475 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____11475 in
                              (uu____11464, true)
                          | uu____11508 when Prims.op_Negation norm1 ->
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
                          | uu____11510 ->
                              let uu____11511 =
                                let uu____11512 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11513 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11512
                                  uu____11513 in
                              failwith uu____11511)
                     | uu____11526 ->
                         let uu____11527 =
                           let uu____11528 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11528.FStar_Syntax_Syntax.n in
                         (match uu____11527 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11555 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11555 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11573 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11573 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11621 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11651 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11651
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11659 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11713  ->
                            fun lb  ->
                              match uu____11713 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11764 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11764
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11767 =
                                      let uu____11775 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11775
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11767 with
                                    | (tok,decl,env2) ->
                                        let uu____11800 =
                                          let uu____11807 =
                                            let uu____11813 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11813, tok) in
                                          uu____11807 :: toks in
                                        (uu____11800, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11659 with
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
                        | uu____11915 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11920 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11920 vars)
                            else
                              (let uu____11922 =
                                 let uu____11926 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11926) in
                               FStar_SMTEncoding_Util.mkApp uu____11922) in
                      let uu____11931 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_11934  ->
                                 match uu___116_11934 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11935 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11940 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11940))) in
                      if uu____11931
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11960;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11962;
                                FStar_Syntax_Syntax.lbeff = uu____11963;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____12000 =
                                 let uu____12004 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____12004 with
                                 | (tcenv',uu____12015,e_t) ->
                                     let uu____12019 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12026 -> failwith "Impossible" in
                                     (match uu____12019 with
                                      | (e1,t_norm1) ->
                                          ((let uu___150_12036 = env1 in
                                            {
                                              bindings =
                                                (uu___150_12036.bindings);
                                              depth = (uu___150_12036.depth);
                                              tcenv = tcenv';
                                              warn = (uu___150_12036.warn);
                                              cache = (uu___150_12036.cache);
                                              nolabels =
                                                (uu___150_12036.nolabels);
                                              use_zfuel_name =
                                                (uu___150_12036.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___150_12036.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___150_12036.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____12000 with
                                | (env',e1,t_norm1) ->
                                    let uu____12043 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____12043 with
                                     | ((binders,body,uu____12055,uu____12056),curry)
                                         ->
                                         ((let uu____12063 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____12063
                                           then
                                             let uu____12064 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12065 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12064 uu____12065
                                           else ());
                                          (let uu____12067 =
                                             encode_binders None binders env' in
                                           match uu____12067 with
                                           | (vars,guards,env'1,binder_decls,uu____12083)
                                               ->
                                               let body1 =
                                                 let uu____12091 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12091
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12094 =
                                                 let uu____12099 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12099
                                                 then
                                                   let uu____12105 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12106 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12105, uu____12106)
                                                 else
                                                   (let uu____12112 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12112)) in
                                               (match uu____12094 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12126 =
                                                        let uu____12130 =
                                                          let uu____12131 =
                                                            let uu____12137 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12137) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12131 in
                                                        let uu____12143 =
                                                          let uu____12145 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12145 in
                                                        (uu____12130,
                                                          uu____12143,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12126 in
                                                    let uu____12147 =
                                                      let uu____12149 =
                                                        let uu____12151 =
                                                          let uu____12153 =
                                                            let uu____12155 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12155 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12153 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12151 in
                                                      FStar_List.append
                                                        decls1 uu____12149 in
                                                    (uu____12147, env1))))))
                           | uu____12158 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12177 = varops.fresh "fuel" in
                             (uu____12177, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12180 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12230  ->
                                     fun uu____12231  ->
                                       match (uu____12230, uu____12231) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12309 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12309 in
                                           let gtok =
                                             let uu____12311 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12311 in
                                           let env3 =
                                             let uu____12313 =
                                               let uu____12315 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12315 in
                                             push_free_var env2 flid gtok
                                               uu____12313 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12180 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12401
                                 t_norm uu____12403 =
                                 match (uu____12401, uu____12403) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12430;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12431;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12448 =
                                       let uu____12452 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12452 with
                                       | (tcenv',uu____12467,e_t) ->
                                           let uu____12471 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12478 ->
                                                 failwith "Impossible" in
                                           (match uu____12471 with
                                            | (e1,t_norm1) ->
                                                ((let uu___151_12488 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___151_12488.bindings);
                                                    depth =
                                                      (uu___151_12488.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___151_12488.warn);
                                                    cache =
                                                      (uu___151_12488.cache);
                                                    nolabels =
                                                      (uu___151_12488.nolabels);
                                                    use_zfuel_name =
                                                      (uu___151_12488.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___151_12488.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___151_12488.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12448 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12498 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12498
                                            then
                                              let uu____12499 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12500 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12501 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12499 uu____12500
                                                uu____12501
                                            else ());
                                           (let uu____12503 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12503 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12525 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12525
                                                  then
                                                    let uu____12526 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12527 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12528 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12529 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12526 uu____12527
                                                      uu____12528 uu____12529
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12533 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12533 with
                                                  | (vars,guards,env'1,binder_decls,uu____12551)
                                                      ->
                                                      let decl_g =
                                                        let uu____12559 =
                                                          let uu____12565 =
                                                            let uu____12567 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12567 in
                                                          (g, uu____12565,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12559 in
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
                                                        let uu____12582 =
                                                          let uu____12586 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12586) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12582 in
                                                      let gsapp =
                                                        let uu____12592 =
                                                          let uu____12596 =
                                                            let uu____12598 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12598 ::
                                                              vars_tm in
                                                          (g, uu____12596) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12592 in
                                                      let gmax =
                                                        let uu____12602 =
                                                          let uu____12606 =
                                                            let uu____12608 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12608 ::
                                                              vars_tm in
                                                          (g, uu____12606) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12602 in
                                                      let body1 =
                                                        let uu____12612 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12612
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12614 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12614 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12625
                                                               =
                                                               let uu____12629
                                                                 =
                                                                 let uu____12630
                                                                   =
                                                                   let uu____12638
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
                                                                    uu____12638) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12630 in
                                                               let uu____12649
                                                                 =
                                                                 let uu____12651
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12651 in
                                                               (uu____12629,
                                                                 uu____12649,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12625 in
                                                           let eqn_f =
                                                             let uu____12654
                                                               =
                                                               let uu____12658
                                                                 =
                                                                 let uu____12659
                                                                   =
                                                                   let uu____12665
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12665) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12659 in
                                                               (uu____12658,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12654 in
                                                           let eqn_g' =
                                                             let uu____12673
                                                               =
                                                               let uu____12677
                                                                 =
                                                                 let uu____12678
                                                                   =
                                                                   let uu____12684
                                                                    =
                                                                    let uu____12685
                                                                    =
                                                                    let uu____12688
                                                                    =
                                                                    let uu____12689
                                                                    =
                                                                    let uu____12693
                                                                    =
                                                                    let uu____12695
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12695
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12693) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12689 in
                                                                    (gsapp,
                                                                    uu____12688) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12685 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12684) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12678 in
                                                               (uu____12677,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12673 in
                                                           let uu____12707 =
                                                             let uu____12712
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12712
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12729)
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
                                                                    let uu____12744
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12744
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12747
                                                                    =
                                                                    let uu____12751
                                                                    =
                                                                    let uu____12752
                                                                    =
                                                                    let uu____12758
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12758) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12752 in
                                                                    (uu____12751,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12747 in
                                                                 let uu____12769
                                                                   =
                                                                   let uu____12773
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12773
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12781
                                                                    =
                                                                    let uu____12783
                                                                    =
                                                                    let uu____12784
                                                                    =
                                                                    let uu____12788
                                                                    =
                                                                    let uu____12789
                                                                    =
                                                                    let uu____12795
                                                                    =
                                                                    let uu____12796
                                                                    =
                                                                    let uu____12799
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12799,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12796 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12795) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12789 in
                                                                    (uu____12788,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12784 in
                                                                    [uu____12783] in
                                                                    (d3,
                                                                    uu____12781) in
                                                                 (match uu____12769
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12707
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
                               let uu____12834 =
                                 let uu____12841 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12889  ->
                                      fun uu____12890  ->
                                        match (uu____12889, uu____12890) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12976 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12976 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12841 in
                               (match uu____12834 with
                                | (decls2,eqns,env01) ->
                                    let uu____13016 =
                                      let isDeclFun uu___117_13024 =
                                        match uu___117_13024 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____13025 -> true
                                        | uu____13031 -> false in
                                      let uu____13032 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____13032
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____13016 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____13062 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____13062
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
        let uu____13096 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13096 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____13099 = encode_sigelt' env se in
      match uu____13099 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13109 =
                  let uu____13110 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13110 in
                [uu____13109]
            | uu____13111 ->
                let uu____13112 =
                  let uu____13114 =
                    let uu____13115 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13115 in
                  uu____13114 :: g in
                let uu____13116 =
                  let uu____13118 =
                    let uu____13119 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13119 in
                  [uu____13118] in
                FStar_List.append uu____13112 uu____13116 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____13129 =
          let uu____13130 = FStar_Syntax_Subst.compress t in
          uu____13130.FStar_Syntax_Syntax.n in
        match uu____13129 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____13134)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____13137 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13140 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13143 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13145 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13147 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13155 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13158 =
            let uu____13159 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13159 Prims.op_Negation in
          if uu____13158
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13179 ->
                   let uu____13180 =
                     let uu____13183 =
                       let uu____13184 =
                         let uu____13199 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13199) in
                       FStar_Syntax_Syntax.Tm_abs uu____13184 in
                     FStar_Syntax_Syntax.mk uu____13183 in
                   uu____13180 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13252 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13252 with
               | (aname,atok,env2) ->
                   let uu____13262 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13262 with
                    | (formals,uu____13272) ->
                        let uu____13279 =
                          let uu____13282 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13282 env2 in
                        (match uu____13279 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13290 =
                                 let uu____13291 =
                                   let uu____13297 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13306  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13297,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13291 in
                               [uu____13290;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13313 =
                               let aux uu____13342 uu____13343 =
                                 match (uu____13342, uu____13343) with
                                 | ((bv,uu____13370),(env3,acc_sorts,acc)) ->
                                     let uu____13391 = gen_term_var env3 bv in
                                     (match uu____13391 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13313 with
                              | (uu____13429,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13443 =
                                      let uu____13447 =
                                        let uu____13448 =
                                          let uu____13454 =
                                            let uu____13455 =
                                              let uu____13458 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13458) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13455 in
                                          ([[app]], xs_sorts, uu____13454) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13448 in
                                      (uu____13447, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13443 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13470 =
                                      let uu____13474 =
                                        let uu____13475 =
                                          let uu____13481 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13481) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13475 in
                                      (uu____13474,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13470 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13491 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13491 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13507,uu____13508)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13509 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13509 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13520,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13525 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13528  ->
                      match uu___118_13528 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13529 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13532 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13533 -> false)) in
            Prims.op_Negation uu____13525 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13539 = encode_top_level_val env fv t quals in
             match uu____13539 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13551 =
                   let uu____13553 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13553 in
                 (uu____13551, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____13559 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____13559 with
           | (uu____13564,f1) ->
               let uu____13566 = encode_formula f1 env in
               (match uu____13566 with
                | (f2,decls) ->
                    let g =
                      let uu____13575 =
                        let uu____13576 =
                          let uu____13580 =
                            let uu____13582 =
                              let uu____13583 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____13583 in
                            Some uu____13582 in
                          let uu____13584 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____13580, uu____13584) in
                        FStar_SMTEncoding_Util.mkAssume uu____13576 in
                      [uu____13575] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13588,attrs) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right attrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let uu____13596 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13611 =
                       let uu____13613 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13613.FStar_Syntax_Syntax.fv_name in
                     uu____13611.FStar_Syntax_Syntax.v in
                   let uu____13614 =
                     let uu____13615 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13615 in
                   if uu____13614
                   then
                     let val_decl =
                       let uu___152_13630 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___152_13630.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___152_13630.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13634 = encode_sigelt' env1 val_decl in
                     match uu____13634 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____13596 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13651,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13653;
                          FStar_Syntax_Syntax.lbtyp = uu____13654;
                          FStar_Syntax_Syntax.lbeff = uu____13655;
                          FStar_Syntax_Syntax.lbdef = uu____13656;_}::[]),uu____13657,uu____13658)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13672 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13672 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13691 =
                   let uu____13693 =
                     let uu____13694 =
                       let uu____13698 =
                         let uu____13699 =
                           let uu____13705 =
                             let uu____13706 =
                               let uu____13709 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13709) in
                             FStar_SMTEncoding_Util.mkEq uu____13706 in
                           ([[b2t_x]], [xx], uu____13705) in
                         FStar_SMTEncoding_Util.mkForall uu____13699 in
                       (uu____13698, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13694 in
                   [uu____13693] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13691 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13726,uu____13727,uu____13728)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_13736  ->
                  match uu___119_13736 with
                  | FStar_Syntax_Syntax.Discriminator uu____13737 -> true
                  | uu____13738 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13740,lids,uu____13742) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13751 =
                     let uu____13752 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13752.FStar_Ident.idText in
                   uu____13751 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_13755  ->
                     match uu___120_13755 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13756 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13759,uu____13760)
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
          let uu____13779 = try_lookup_free_var env l in
          (match uu____13779 with
           | Some uu____13783 -> ([], env)
           | None  ->
               let se1 =
                 let uu___153_13786 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___153_13786.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___153_13786.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13792,uu____13793) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13805) ->
          let uu____13810 = encode_sigelts env ses in
          (match uu____13810 with
           | (g,env1) ->
               let uu____13820 =
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
               (match uu____13820 with
                | (g',inversions) ->
                    let uu____13848 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_13860  ->
                              match uu___123_13860 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13861 ->
                                  true
                              | uu____13867 -> false)) in
                    (match uu____13848 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13878,tps,k,uu____13881,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_13892  ->
                    match uu___124_13892 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13893 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13900 = c in
              match uu____13900 with
              | (name,args,uu____13904,uu____13905,uu____13906) ->
                  let uu____13909 =
                    let uu____13910 =
                      let uu____13916 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13927  ->
                                match uu____13927 with
                                | (uu____13931,sort,uu____13933) -> sort)) in
                      (name, uu____13916, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13910 in
                  [uu____13909]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13951 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13956 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13956 FStar_Option.isNone)) in
            if uu____13951
            then []
            else
              (let uu____13973 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13973 with
               | (xxsym,xx) ->
                   let uu____13979 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____14008  ->
                             fun l  ->
                               match uu____14008 with
                               | (out,decls) ->
                                   let uu____14020 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____14020 with
                                    | (uu____14026,data_t) ->
                                        let uu____14028 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____14028 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____14057 =
                                                 let uu____14058 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____14058.FStar_Syntax_Syntax.n in
                                               match uu____14057 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____14066,indices) ->
                                                   indices
                                               | uu____14082 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____14099  ->
                                                         match uu____14099
                                                         with
                                                         | (x,uu____14103) ->
                                                             let uu____14104
                                                               =
                                                               let uu____14105
                                                                 =
                                                                 let uu____14109
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____14109,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14105 in
                                                             push_term_var
                                                               env1 x
                                                               uu____14104)
                                                    env) in
                                             let uu____14111 =
                                               encode_args indices env1 in
                                             (match uu____14111 with
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
                                                      let uu____14131 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14142
                                                                 =
                                                                 let uu____14145
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____14145,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14142)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____14131
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____14147 =
                                                      let uu____14148 =
                                                        let uu____14151 =
                                                          let uu____14152 =
                                                            let uu____14155 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____14155,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14152 in
                                                        (out, uu____14151) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14148 in
                                                    (uu____14147,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13979 with
                    | (data_ax,decls) ->
                        let uu____14163 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14163 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14174 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14174 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14177 =
                                 let uu____14181 =
                                   let uu____14182 =
                                     let uu____14188 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14196 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14188,
                                       uu____14196) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14182 in
                                 let uu____14204 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14181, (Some "inversion axiom"),
                                   uu____14204) in
                               FStar_SMTEncoding_Util.mkAssume uu____14177 in
                             let pattern_guarded_inversion =
                               let uu____14208 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14208
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14216 =
                                   let uu____14217 =
                                     let uu____14221 =
                                       let uu____14222 =
                                         let uu____14228 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14236 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14228, uu____14236) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14222 in
                                     let uu____14244 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14221, (Some "inversion axiom"),
                                       uu____14244) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14217 in
                                 [uu____14216]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14247 =
            let uu____14255 =
              let uu____14256 = FStar_Syntax_Subst.compress k in
              uu____14256.FStar_Syntax_Syntax.n in
            match uu____14255 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14285 -> (tps, k) in
          (match uu____14247 with
           | (formals,res) ->
               let uu____14300 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14300 with
                | (formals1,res1) ->
                    let uu____14307 = encode_binders None formals1 env in
                    (match uu____14307 with
                     | (vars,guards,env',binder_decls,uu____14322) ->
                         let uu____14329 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14329 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14342 =
                                  let uu____14346 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14346) in
                                FStar_SMTEncoding_Util.mkApp uu____14342 in
                              let uu____14351 =
                                let tname_decl =
                                  let uu____14357 =
                                    let uu____14358 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14376  ->
                                              match uu____14376 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14384 = varops.next_id () in
                                    (tname, uu____14358,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14384, false) in
                                  constructor_or_logic_type_decl uu____14357 in
                                let uu____14389 =
                                  match vars with
                                  | [] ->
                                      let uu____14396 =
                                        let uu____14397 =
                                          let uu____14399 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
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
                              (match uu____14351 with
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
                                          let uu____14615 =
                                            mk_term_projector_name d x in
                                          (uu____14615,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14617 =
                                  let uu____14627 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14627, true) in
                                FStar_All.pipe_right uu____14617
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
                              let uu____14649 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14649 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14657::uu____14658 ->
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
                                         let uu____14683 =
                                           let uu____14689 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14689) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14683
                                     | uu____14702 -> tok_typing in
                                   let uu____14707 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14707 with
                                    | (vars',guards',env'',decls_formals,uu____14722)
                                        ->
                                        let uu____14729 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14729 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14748 ->
                                                   let uu____14752 =
                                                     let uu____14753 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14753 in
                                                   [uu____14752] in
                                             let encode_elim uu____14760 =
                                               let uu____14761 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14761 with
                                               | (head1,args) ->
                                                   let uu____14790 =
                                                     let uu____14791 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14791.FStar_Syntax_Syntax.n in
                                                   (match uu____14790 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____14798;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14799;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14800;_},uu____14801)
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
                                                                    let uu____14844
                                                                    =
                                                                    let uu____14845
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14845 in
                                                                    if
                                                                    uu____14844
                                                                    then
                                                                    let uu____14852
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14852]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14854
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14878
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14878
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14900
                                                                    =
                                                                    let uu____14904
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14904 in
                                                                    (match uu____14900
                                                                    with
                                                                    | 
                                                                    (uu____14911,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14917
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14917
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14919
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14919
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
                                                             (match uu____14854
                                                              with
                                                              | (uu____14927,arg_vars,elim_eqns_or_guards,uu____14930)
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
                                                                    let uu____14949
                                                                    =
                                                                    let uu____14953
                                                                    =
                                                                    let uu____14954
                                                                    =
                                                                    let uu____14960
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14966
                                                                    =
                                                                    let uu____14967
                                                                    =
                                                                    let uu____14970
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14970) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14967 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14960,
                                                                    uu____14966) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14954 in
                                                                    (uu____14953,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14949 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14983
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14983,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14985
                                                                    =
                                                                    let uu____14989
                                                                    =
                                                                    let uu____14990
                                                                    =
                                                                    let uu____14996
                                                                    =
                                                                    let uu____14999
                                                                    =
                                                                    let uu____15001
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15001] in
                                                                    [uu____14999] in
                                                                    let uu____15004
                                                                    =
                                                                    let uu____15005
                                                                    =
                                                                    let uu____15008
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15009
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15008,
                                                                    uu____15009) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15005 in
                                                                    (uu____14996,
                                                                    [x],
                                                                    uu____15004) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14990 in
                                                                    let uu____15019
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14989,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15019) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14985
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15024
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
                                                                    (let uu____15041
                                                                    =
                                                                    let uu____15042
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15042
                                                                    dapp1 in
                                                                    [uu____15041]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15024
                                                                    FStar_List.flatten in
                                                                    let uu____15046
                                                                    =
                                                                    let uu____15050
                                                                    =
                                                                    let uu____15051
                                                                    =
                                                                    let uu____15057
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15063
                                                                    =
                                                                    let uu____15064
                                                                    =
                                                                    let uu____15067
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15067) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15064 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15057,
                                                                    uu____15063) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15051 in
                                                                    (uu____15050,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15046) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____15079 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15079
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
                                                                 | uu____15105
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15116
                                                                    =
                                                                    let uu____15117
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15117 in
                                                                    if
                                                                    uu____15116
                                                                    then
                                                                    let uu____15124
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15124]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15126
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15150
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15150
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15172
                                                                    =
                                                                    let uu____15176
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15176 in
                                                                    (match uu____15172
                                                                    with
                                                                    | 
                                                                    (uu____15183,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15189
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15189
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15191
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15191
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
                                                             (match uu____15126
                                                              with
                                                              | (uu____15199,arg_vars,elim_eqns_or_guards,uu____15202)
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
                                                                    let uu____15221
                                                                    =
                                                                    let uu____15225
                                                                    =
                                                                    let uu____15226
                                                                    =
                                                                    let uu____15232
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15238
                                                                    =
                                                                    let uu____15239
                                                                    =
                                                                    let uu____15242
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15242) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15239 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15232,
                                                                    uu____15238) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15226 in
                                                                    (uu____15225,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15221 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15255
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15255,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15257
                                                                    =
                                                                    let uu____15261
                                                                    =
                                                                    let uu____15262
                                                                    =
                                                                    let uu____15268
                                                                    =
                                                                    let uu____15271
                                                                    =
                                                                    let uu____15273
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15273] in
                                                                    [uu____15271] in
                                                                    let uu____15276
                                                                    =
                                                                    let uu____15277
                                                                    =
                                                                    let uu____15280
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15281
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15280,
                                                                    uu____15281) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15277 in
                                                                    (uu____15268,
                                                                    [x],
                                                                    uu____15276) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15262 in
                                                                    let uu____15291
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15261,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15291) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15257
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15296
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
                                                                    (let uu____15313
                                                                    =
                                                                    let uu____15314
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15314
                                                                    dapp1 in
                                                                    [uu____15313]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15296
                                                                    FStar_List.flatten in
                                                                    let uu____15318
                                                                    =
                                                                    let uu____15322
                                                                    =
                                                                    let uu____15323
                                                                    =
                                                                    let uu____15329
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15335
                                                                    =
                                                                    let uu____15336
                                                                    =
                                                                    let uu____15339
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15339) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15336 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15329,
                                                                    uu____15335) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15323 in
                                                                    (uu____15322,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15318) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15349 ->
                                                        ((let uu____15351 =
                                                            let uu____15352 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15353 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15352
                                                              uu____15353 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15351);
                                                         ([], []))) in
                                             let uu____15356 = encode_elim () in
                                             (match uu____15356 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15368 =
                                                      let uu____15370 =
                                                        let uu____15372 =
                                                          let uu____15374 =
                                                            let uu____15376 =
                                                              let uu____15377
                                                                =
                                                                let uu____15383
                                                                  =
                                                                  let uu____15385
                                                                    =
                                                                    let uu____15386
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15386 in
                                                                  Some
                                                                    uu____15385 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15383) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15377 in
                                                            [uu____15376] in
                                                          let uu____15389 =
                                                            let uu____15391 =
                                                              let uu____15393
                                                                =
                                                                let uu____15395
                                                                  =
                                                                  let uu____15397
                                                                    =
                                                                    let uu____15399
                                                                    =
                                                                    let uu____15401
                                                                    =
                                                                    let uu____15402
                                                                    =
                                                                    let uu____15406
                                                                    =
                                                                    let uu____15407
                                                                    =
                                                                    let uu____15413
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15413) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15407 in
                                                                    (uu____15406,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15402 in
                                                                    let uu____15420
                                                                    =
                                                                    let uu____15422
                                                                    =
                                                                    let uu____15423
                                                                    =
                                                                    let uu____15427
                                                                    =
                                                                    let uu____15428
                                                                    =
                                                                    let uu____15434
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____15440
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15434,
                                                                    uu____15440) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15428 in
                                                                    (uu____15427,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15423 in
                                                                    [uu____15422] in
                                                                    uu____15401
                                                                    ::
                                                                    uu____15420 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15399 in
                                                                  FStar_List.append
                                                                    uu____15397
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15395 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15393 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15391 in
                                                          FStar_List.append
                                                            uu____15374
                                                            uu____15389 in
                                                        FStar_List.append
                                                          decls3 uu____15372 in
                                                      FStar_List.append
                                                        decls2 uu____15370 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15368 in
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
           (fun uu____15468  ->
              fun se  ->
                match uu____15468 with
                | (g,env1) ->
                    let uu____15480 = encode_sigelt env1 se in
                    (match uu____15480 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15516 =
        match uu____15516 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15534 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____15539 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15539
                   then
                     let uu____15540 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15541 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15542 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15540 uu____15541 uu____15542
                   else ());
                  (let uu____15544 = encode_term t1 env1 in
                   match uu____15544 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15554 =
                         let uu____15558 =
                           let uu____15559 =
                             let uu____15560 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15560
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15559 in
                         new_term_constant_from_string env1 x uu____15558 in
                       (match uu____15554 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15571 = FStar_Options.log_queries () in
                              if uu____15571
                              then
                                let uu____15573 =
                                  let uu____15574 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15575 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15576 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15574 uu____15575 uu____15576 in
                                Some uu____15573
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15587,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15596 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15596 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15609,se,uu____15611) ->
                 let uu____15614 = encode_sigelt env1 se in
                 (match uu____15614 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15624,se) ->
                 let uu____15628 = encode_sigelt env1 se in
                 (match uu____15628 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15638 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15638 with | (uu____15650,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15699  ->
            match uu____15699 with
            | (l,uu____15706,uu____15707) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15734  ->
            match uu____15734 with
            | (l,uu____15742,uu____15743) ->
                let uu____15748 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39) (
                    fst l) in
                let uu____15749 =
                  let uu____15751 =
                    let uu____15752 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15752 in
                  [uu____15751] in
                uu____15748 :: uu____15749)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15763 =
      let uu____15765 =
        let uu____15766 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15768 =
          let uu____15769 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15769 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15766;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15768
        } in
      [uu____15765] in
    FStar_ST.write last_env uu____15763
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15779 = FStar_ST.read last_env in
      match uu____15779 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15785 ->
          let uu___154_15787 = e in
          let uu____15788 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___154_15787.bindings);
            depth = (uu___154_15787.depth);
            tcenv;
            warn = (uu___154_15787.warn);
            cache = (uu___154_15787.cache);
            nolabels = (uu___154_15787.nolabels);
            use_zfuel_name = (uu___154_15787.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15787.encode_non_total_function_typ);
            current_module_name = uu____15788
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15792 = FStar_ST.read last_env in
    match uu____15792 with
    | [] -> failwith "Empty env stack"
    | uu____15797::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15805  ->
    let uu____15806 = FStar_ST.read last_env in
    match uu____15806 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___155_15817 = hd1 in
          {
            bindings = (uu___155_15817.bindings);
            depth = (uu___155_15817.depth);
            tcenv = (uu___155_15817.tcenv);
            warn = (uu___155_15817.warn);
            cache = refs;
            nolabels = (uu___155_15817.nolabels);
            use_zfuel_name = (uu___155_15817.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_15817.encode_non_total_function_typ);
            current_module_name = (uu___155_15817.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15823  ->
    let uu____15824 = FStar_ST.read last_env in
    match uu____15824 with
    | [] -> failwith "Popping an empty stack"
    | uu____15829::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15837  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15840  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15843  ->
    let uu____15844 = FStar_ST.read last_env in
    match uu____15844 with
    | hd1::uu____15850::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15856 -> failwith "Impossible"
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
        | (uu____15905::uu____15906,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___156_15912 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___156_15912.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___156_15912.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___156_15912.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15913 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15924 =
        let uu____15926 =
          let uu____15927 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15927 in
        let uu____15928 = open_fact_db_tags env in uu____15926 :: uu____15928 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15924
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
      let uu____15943 = encode_sigelt env se in
      match uu____15943 with
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
        let uu____15968 = FStar_Options.log_queries () in
        if uu____15968
        then
          let uu____15970 =
            let uu____15971 =
              let uu____15972 =
                let uu____15973 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15973 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15972 in
            FStar_SMTEncoding_Term.Caption uu____15971 in
          uu____15970 :: decls
        else decls in
      let env =
        let uu____15980 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15980 tcenv in
      let uu____15981 = encode_top_level_facts env se in
      match uu____15981 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15990 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15990))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____16001 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____16001
       then
         let uu____16002 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____16002
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____16030  ->
                 fun se  ->
                   match uu____16030 with
                   | (g,env2) ->
                       let uu____16042 = encode_top_level_facts env2 se in
                       (match uu____16042 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____16055 =
         encode_signature
           (let uu___157_16061 = env in
            {
              bindings = (uu___157_16061.bindings);
              depth = (uu___157_16061.depth);
              tcenv = (uu___157_16061.tcenv);
              warn = false;
              cache = (uu___157_16061.cache);
              nolabels = (uu___157_16061.nolabels);
              use_zfuel_name = (uu___157_16061.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___157_16061.encode_non_total_function_typ);
              current_module_name = (uu___157_16061.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____16055 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____16073 = FStar_Options.log_queries () in
             if uu____16073
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___158_16080 = env1 in
               {
                 bindings = (uu___158_16080.bindings);
                 depth = (uu___158_16080.depth);
                 tcenv = (uu___158_16080.tcenv);
                 warn = true;
                 cache = (uu___158_16080.cache);
                 nolabels = (uu___158_16080.nolabels);
                 use_zfuel_name = (uu___158_16080.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___158_16080.encode_non_total_function_typ);
                 current_module_name = (uu___158_16080.current_module_name)
               });
            (let uu____16082 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____16082
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
        (let uu____16117 =
           let uu____16118 = FStar_TypeChecker_Env.current_module tcenv in
           uu____16118.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16117);
        (let env =
           let uu____16120 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____16120 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____16129 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16150 = aux rest in
                 (match uu____16150 with
                  | (out,rest1) ->
                      let t =
                        let uu____16168 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____16168 with
                        | Some uu____16172 ->
                            let uu____16173 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16173
                              x.FStar_Syntax_Syntax.sort
                        | uu____16174 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____16177 =
                        let uu____16179 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___159_16182 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___159_16182.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___159_16182.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16179 :: out in
                      (uu____16177, rest1))
             | uu____16185 -> ([], bindings1) in
           let uu____16189 = aux bindings in
           match uu____16189 with
           | (closing,bindings1) ->
               let uu____16203 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16203, bindings1) in
         match uu____16129 with
         | (q1,bindings1) ->
             let uu____16216 =
               let uu____16219 =
                 FStar_List.filter
                   (fun uu___125_16223  ->
                      match uu___125_16223 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16224 ->
                          false
                      | uu____16228 -> true) bindings1 in
               encode_env_bindings env uu____16219 in
             (match uu____16216 with
              | (env_decls,env1) ->
                  ((let uu____16239 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16239
                    then
                      let uu____16240 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16240
                    else ());
                   (let uu____16242 = encode_formula q1 env1 in
                    match uu____16242 with
                    | (phi,qdecls) ->
                        let uu____16254 =
                          let uu____16257 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16257 phi in
                        (match uu____16254 with
                         | (labels,phi1) ->
                             let uu____16267 = encode_labels labels in
                             (match uu____16267 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____16288 =
                                      let uu____16292 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16293 =
                                        varops.mk_unique "@query" in
                                      (uu____16292, (Some "query"),
                                        uu____16293) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16288 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16306 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16306 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16308 = encode_formula q env in
       match uu____16308 with
       | (f,uu____16312) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16314) -> true
             | uu____16317 -> false)))