open Prims
let add_fuel x tl1 =
  let uu____16 = FStar_Options.unthrottle_inductives () in
  if uu____16 then tl1 else x :: tl1
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___117_74  ->
       match uu___117_74 with
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
        let uu___142_140 = a in
        let uu____141 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___142_140.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___142_140.FStar_Syntax_Syntax.sort)
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
                         mk_term_projector_name lid (Prims.fst b)))
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
      FStar_All.pipe_left Prims.fst uu____498 in
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
          FStar_All.pipe_left Prims.snd uu____596 in
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
    let uu___143_780 = x in
    let uu____781 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____781;
      FStar_Syntax_Syntax.index = (uu___143_780.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___143_780.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term Prims.option* FStar_SMTEncoding_Term.term
  Prims.option)
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
    (FStar_Ident.lident* Prims.string* FStar_SMTEncoding_Term.term
      Prims.option* FStar_SMTEncoding_Term.term Prims.option)
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar v1 = (v1, None)
type cache_entry =
  {
  cache_symbol_name: Prims.string;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list;
  cache_symbol_activate_fact: FStar_SMTEncoding_Term.decl Prims.list;}
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
  current_module_name: Prims.string;
  activate_current_sigelt_facts: FStar_SMTEncoding_Term.decl Prims.list;}
let mk_cache_entry:
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.sort Prims.list ->
        FStar_SMTEncoding_Term.decl Prims.list -> cache_entry
  =
  fun env  ->
    fun tsym  ->
      fun cvar_sorts  ->
        fun t_decls  ->
          {
            cache_symbol_name = tsym;
            cache_symbol_arg_sorts = cvar_sorts;
            cache_symbol_decls = t_decls;
            cache_symbol_activate_fact = (env.activate_current_sigelt_facts)
          }
let get_activation_facts:
  cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun c  ->
    FStar_All.pipe_right c.cache_symbol_activate_fact
      (FStar_List.map
         (fun d  ->
            match d with
            | FStar_SMTEncoding_Term.Assume (t,c1,n1) ->
                let uu____1007 =
                  let uu____1011 = varops.mk_unique n1 in (t, c1, uu____1011) in
                FStar_SMTEncoding_Term.Assume uu____1007
            | d1 -> d1))
let print_env: env_t -> Prims.string =
  fun e  ->
    let uu____1016 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___118_1020  ->
              match uu___118_1020 with
              | Binding_var (x,uu____1022) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1024,uu____1025,uu____1026) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1016 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option
  =
  fun env  ->
    fun t  ->
      let uu____1059 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1059
      then
        let uu____1061 = FStar_Syntax_Print.term_to_string t in
        Some uu____1061
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1072 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1072)
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
        (let uu___144_1084 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___144_1084.tcenv);
           warn = (uu___144_1084.warn);
           cache = (uu___144_1084.cache);
           nolabels = (uu___144_1084.nolabels);
           use_zfuel_name = (uu___144_1084.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___144_1084.encode_non_total_function_typ);
           current_module_name = (uu___144_1084.current_module_name);
           activate_current_sigelt_facts =
             (uu___144_1084.activate_current_sigelt_facts)
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
        (let uu___145_1097 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___145_1097.depth);
           tcenv = (uu___145_1097.tcenv);
           warn = (uu___145_1097.warn);
           cache = (uu___145_1097.cache);
           nolabels = (uu___145_1097.nolabels);
           use_zfuel_name = (uu___145_1097.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___145_1097.encode_non_total_function_typ);
           current_module_name = (uu___145_1097.current_module_name);
           activate_current_sigelt_facts =
             (uu___145_1097.activate_current_sigelt_facts)
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
          (let uu___146_1113 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___146_1113.depth);
             tcenv = (uu___146_1113.tcenv);
             warn = (uu___146_1113.warn);
             cache = (uu___146_1113.cache);
             nolabels = (uu___146_1113.nolabels);
             use_zfuel_name = (uu___146_1113.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___146_1113.encode_non_total_function_typ);
             current_module_name = (uu___146_1113.current_module_name);
             activate_current_sigelt_facts =
               (uu___146_1113.activate_current_sigelt_facts)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___147_1123 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___147_1123.depth);
          tcenv = (uu___147_1123.tcenv);
          warn = (uu___147_1123.warn);
          cache = (uu___147_1123.cache);
          nolabels = (uu___147_1123.nolabels);
          use_zfuel_name = (uu___147_1123.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___147_1123.encode_non_total_function_typ);
          current_module_name = (uu___147_1123.current_module_name);
          activate_current_sigelt_facts =
            (uu___147_1123.activate_current_sigelt_facts)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___119_1139  ->
             match uu___119_1139 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1147 -> None) in
      let uu____1150 = aux a in
      match uu____1150 with
      | None  ->
          let a2 = unmangle a in
          let uu____1157 = aux a2 in
          (match uu____1157 with
           | None  ->
               let uu____1163 =
                 let uu____1164 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1165 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1164 uu____1165 in
               failwith uu____1163
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1185 =
        let uu___148_1186 = env in
        let uu____1187 =
          let uu____1189 =
            let uu____1190 =
              let uu____1197 =
                let uu____1199 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1199 in
              (x, fname, uu____1197, None) in
            Binding_fvar uu____1190 in
          uu____1189 :: (env.bindings) in
        {
          bindings = uu____1187;
          depth = (uu___148_1186.depth);
          tcenv = (uu___148_1186.tcenv);
          warn = (uu___148_1186.warn);
          cache = (uu___148_1186.cache);
          nolabels = (uu___148_1186.nolabels);
          use_zfuel_name = (uu___148_1186.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___148_1186.encode_non_total_function_typ);
          current_module_name = (uu___148_1186.current_module_name);
          activate_current_sigelt_facts =
            (uu___148_1186.activate_current_sigelt_facts)
        } in
      (fname, ftok, uu____1185)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___120_1221  ->
           match uu___120_1221 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1243 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1255 =
        lookup_binding env
          (fun uu___121_1257  ->
             match uu___121_1257 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1267 -> None) in
      FStar_All.pipe_right uu____1255 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1280 = try_lookup_lid env a in
      match uu____1280 with
      | None  ->
          let uu____1297 =
            let uu____1298 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1298 in
          failwith uu____1297
      | Some s -> s
let push_free_var:
  env_t ->
    FStar_Ident.lident ->
      Prims.string -> FStar_SMTEncoding_Term.term Prims.option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___149_1329 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___149_1329.depth);
            tcenv = (uu___149_1329.tcenv);
            warn = (uu___149_1329.warn);
            cache = (uu___149_1329.cache);
            nolabels = (uu___149_1329.nolabels);
            use_zfuel_name = (uu___149_1329.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___149_1329.encode_non_total_function_typ);
            current_module_name = (uu___149_1329.current_module_name);
            activate_current_sigelt_facts =
              (uu___149_1329.activate_current_sigelt_facts)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1341 = lookup_lid env x in
        match uu____1341 with
        | (t1,t2,uu____1349) ->
            let t3 =
              let uu____1355 =
                let uu____1359 =
                  let uu____1361 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1361] in
                (f, uu____1359) in
              FStar_SMTEncoding_Util.mkApp uu____1355 in
            let uu___150_1364 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___150_1364.depth);
              tcenv = (uu___150_1364.tcenv);
              warn = (uu___150_1364.warn);
              cache = (uu___150_1364.cache);
              nolabels = (uu___150_1364.nolabels);
              use_zfuel_name = (uu___150_1364.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___150_1364.encode_non_total_function_typ);
              current_module_name = (uu___150_1364.current_module_name);
              activate_current_sigelt_facts =
                (uu___150_1364.activate_current_sigelt_facts)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1374 = try_lookup_lid env l in
      match uu____1374 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1401 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1406,fuel::[]) ->
                         let uu____1409 =
                           let uu____1410 =
                             let uu____1411 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1411 Prims.fst in
                           FStar_Util.starts_with uu____1410 "fuel" in
                         if uu____1409
                         then
                           let uu____1413 =
                             let uu____1414 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1414
                               fuel in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1413
                         else Some t
                     | uu____1417 -> Some t)
                | uu____1418 -> None))
let lookup_free_var env a =
  let uu____1436 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1436 with
  | Some t -> t
  | None  ->
      let uu____1439 =
        let uu____1440 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1440 in
      failwith uu____1439
let lookup_free_var_name env a =
  let uu____1457 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1457 with | (x,uu____1464,uu____1465) -> x
let lookup_free_var_sym env a =
  let uu____1489 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1489 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1510;
             FStar_SMTEncoding_Term.rng = uu____1511;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1519 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1533 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___122_1542  ->
           match uu___122_1542 with
           | Binding_fvar (uu____1544,nm',tok,uu____1547) when nm = nm' ->
               tok
           | uu____1552 -> None)
let mkForall_fuel' n1 uu____1569 =
  match uu____1569 with
  | (pats,vars,body) ->
      let fallback uu____1585 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1588 = FStar_Options.unthrottle_inductives () in
      if uu____1588
      then fallback ()
      else
        (let uu____1590 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1590 with
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
                       | uu____1609 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1623 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1623
                     | uu____1625 ->
                         let uu____1626 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1626 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1629 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow _
        |FStar_Syntax_Syntax.Tm_refine _
         |FStar_Syntax_Syntax.Tm_bvar _
          |FStar_Syntax_Syntax.Tm_uvar _
           |FStar_Syntax_Syntax.Tm_abs _|FStar_Syntax_Syntax.Tm_constant _
          -> true
      | FStar_Syntax_Syntax.Tm_fvar fv|FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
           FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
           FStar_Syntax_Syntax.vars = _;_},_)
          ->
          let uu____1673 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1673 FStar_Option.isNone
      | uu____1686 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1693 =
        let uu____1694 = FStar_Syntax_Util.un_uinst t in
        uu____1694.FStar_Syntax_Syntax.n in
      match uu____1693 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1697,uu____1698,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___123_1727  ->
                  match uu___123_1727 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1728 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1729,uu____1730,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1757 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1757 FStar_Option.isSome
      | uu____1770 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1777 = head_normal env t in
      if uu____1777
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
    let uu____1788 =
      let uu____1789 = FStar_Syntax_Syntax.null_binder t in [uu____1789] in
    let uu____1790 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1788 uu____1790 None
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
                match Prims.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____1817 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1817
                | s ->
                    let uu____1820 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1820) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___124_1832  ->
    match uu___124_1832 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1833 -> false
let is_an_eta_expansion:
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term Prims.option
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
                       FStar_SMTEncoding_Term.freevars = uu____1861;
                       FStar_SMTEncoding_Term.rng = uu____1862;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1876) ->
              let uu____1881 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1891 -> false) args (FStar_List.rev xs)) in
              if uu____1881 then tok_of_name env f else None
          | (uu____1894,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1897 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1899 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1899)) in
              if uu____1897 then Some t else None
          | uu____1902 -> None in
        check_partial_applications body (FStar_List.rev vars)
let reify_body:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let tm = FStar_Syntax_Util.mk_reify t in
      let tm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Reify;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm in
      (let uu____1917 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____1917
       then
         let uu____1918 = FStar_Syntax_Print.term_to_string tm in
         let uu____1919 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____1918 uu____1919
       else ());
      tm'
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
    | uu____2001 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___125_2004  ->
    match uu___125_2004 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2006 =
          let uu____2010 =
            let uu____2012 =
              let uu____2013 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2013 in
            [uu____2012] in
          ("FStar.Char.Char", uu____2010) in
        FStar_SMTEncoding_Util.mkApp uu____2006
    | FStar_Const.Const_int (i,None ) ->
        let uu____2021 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2021
    | FStar_Const.Const_int (i,Some uu____2023) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2032) ->
        let uu____2035 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2035
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2039 =
          let uu____2040 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2040 in
        failwith uu____2039
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2059 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2067 ->
            let uu____2072 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2072
        | uu____2073 ->
            if norm1
            then let uu____2074 = whnf env t1 in aux false uu____2074
            else
              (let uu____2076 =
                 let uu____2077 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2078 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2077 uu____2078 in
               failwith uu____2076) in
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
    | uu____2099 ->
        let uu____2100 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2100)
let rec encode_binders:
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list* FStar_SMTEncoding_Term.term
          Prims.list* env_t* FStar_SMTEncoding_Term.decls_t*
          FStar_Syntax_Syntax.bv Prims.list)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____2243 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2243
         then
           let uu____2244 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2244
         else ());
        (let uu____2246 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2282  ->
                   fun b  ->
                     match uu____2282 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2325 =
                           let x = unmangle (Prims.fst b) in
                           let uu____2334 = gen_term_var env1 x in
                           match uu____2334 with
                           | (xxsym,xx,env') ->
                               let uu____2348 =
                                 let uu____2351 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2351 env1 xx in
                               (match uu____2348 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2325 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2246 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))
and encode_term_pred:
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2439 = encode_term t env in
          match uu____2439 with
          | (t1,decls) ->
              let uu____2446 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2446, decls)
and encode_term_pred':
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2454 = encode_term t env in
          match uu____2454 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2463 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2463, decls)
               | Some f ->
                   let uu____2465 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2465, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2472 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2472
       then
         let uu____2473 = FStar_Syntax_Print.tag_of_term t in
         let uu____2474 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2475 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2473 uu____2474
           uu____2475
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2480 =
             let uu____2481 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2482 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2483 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2484 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2481
               uu____2482 uu____2483 uu____2484 in
           failwith uu____2480
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2488 =
             let uu____2489 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2489 in
           failwith uu____2488
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2494) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2524) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2533 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2533, [])
       | FStar_Syntax_Syntax.Tm_type uu____2539 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2542) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2548 = encode_const c in (uu____2548, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2563 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2563 with
            | (binders1,res) ->
                let uu____2570 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2570
                then
                  let uu____2573 = encode_binders None binders1 env in
                  (match uu____2573 with
                   | (vars,guards,env',decls,uu____2588) ->
                       let fsym =
                         let uu____2598 = varops.fresh "f" in
                         (uu____2598, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2601 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___151_2605 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___151_2605.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___151_2605.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___151_2605.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___151_2605.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___151_2605.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___151_2605.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___151_2605.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___151_2605.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___151_2605.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___151_2605.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___151_2605.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___151_2605.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___151_2605.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___151_2605.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___151_2605.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___151_2605.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___151_2605.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___151_2605.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___151_2605.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___151_2605.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___151_2605.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___151_2605.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___151_2605.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2601 with
                        | (pre_opt,res_t) ->
                            let uu____2612 =
                              encode_term_pred None res_t env' app in
                            (match uu____2612 with
                             | (res_pred,decls') ->
                                 let uu____2619 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2626 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2626, [])
                                   | Some pre ->
                                       let uu____2629 =
                                         encode_formula pre env' in
                                       (match uu____2629 with
                                        | (guard,decls0) ->
                                            let uu____2637 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2637, decls0)) in
                                 (match uu____2619 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2645 =
                                          let uu____2651 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2651) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2645 in
                                      let cvars =
                                        let uu____2661 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2661
                                          (FStar_List.filter
                                             (fun uu____2667  ->
                                                match uu____2667 with
                                                | (x,uu____2671) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2682 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2682 with
                                       | Some cache_entry ->
                                           let uu____2687 =
                                             let uu____2688 =
                                               let uu____2692 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____2692) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2688 in
                                           let uu____2701 =
                                             get_activation_facts cache_entry in
                                           (uu____2687, uu____2701)
                                       | None  ->
                                           let tsym =
                                             let uu____2705 =
                                               let uu____2706 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2706 in
                                             varops.mk_unique uu____2705 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2713 =
                                               FStar_Options.log_queries () in
                                             if uu____2713
                                             then
                                               let uu____2715 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2715
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2721 =
                                               let uu____2725 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2725) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2721 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____2733 =
                                               let uu____2737 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2737, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2733 in
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
                                             let uu____2750 =
                                               let uu____2754 =
                                                 let uu____2755 =
                                                   let uu____2761 =
                                                     let uu____2762 =
                                                       let uu____2765 =
                                                         let uu____2766 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2766 in
                                                       (f_has_t, uu____2765) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2762 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2761) in
                                                 mkForall_fuel uu____2755 in
                                               (uu____2754,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2750 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____2779 =
                                               let uu____2783 =
                                                 let uu____2784 =
                                                   let uu____2790 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2790) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2784 in
                                               (uu____2783, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2779 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           (FStar_Util.smap_add env.cache
                                              tkey_hash
                                              (mk_cache_entry env tsym
                                                 cvar_sorts t_decls);
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
                     let uu____2814 =
                       let uu____2818 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____2818, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Term.Assume uu____2814 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____2827 =
                       let uu____2831 =
                         let uu____2832 =
                           let uu____2838 =
                             let uu____2839 =
                               let uu____2842 =
                                 let uu____2843 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2843 in
                               (f_has_t, uu____2842) in
                             FStar_SMTEncoding_Util.mkImp uu____2839 in
                           ([[f_has_t]], [fsym], uu____2838) in
                         mkForall_fuel uu____2832 in
                       (uu____2831, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Term.Assume uu____2827 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2857 ->
           let uu____2862 =
             let uu____2865 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2865 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2870;
                 FStar_Syntax_Syntax.pos = uu____2871;
                 FStar_Syntax_Syntax.vars = uu____2872;_} ->
                 let uu____2879 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2879 with
                  | (b,f1) ->
                      let uu____2893 =
                        let uu____2894 = FStar_List.hd b in
                        Prims.fst uu____2894 in
                      (uu____2893, f1))
             | uu____2899 -> failwith "impossible" in
           (match uu____2862 with
            | (x,f) ->
                let uu____2906 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____2906 with
                 | (base_t,decls) ->
                     let uu____2913 = gen_term_var env x in
                     (match uu____2913 with
                      | (x1,xtm,env') ->
                          let uu____2922 = encode_formula f env' in
                          (match uu____2922 with
                           | (refinement,decls') ->
                               let uu____2929 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____2929 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____2940 =
                                        let uu____2942 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____2946 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____2942
                                          uu____2946 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____2940 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____2962  ->
                                              match uu____2962 with
                                              | (y,uu____2966) ->
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
                                    let uu____2985 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2985 with
                                     | Some cache_entry ->
                                         let uu____2990 =
                                           let uu____2991 =
                                             let uu____2995 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____2995) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2991 in
                                         let uu____3004 =
                                           get_activation_facts cache_entry in
                                         (uu____2990, uu____3004)
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3009 =
                                             let uu____3010 =
                                               let uu____3011 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3011 in
                                             Prims.strcat module_name
                                               uu____3010 in
                                           varops.mk_unique uu____3009 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3020 =
                                             let uu____3024 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3024) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3020 in
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
                                           let uu____3034 =
                                             let uu____3038 =
                                               let uu____3039 =
                                                 let uu____3045 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3045) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3039 in
                                             (uu____3038,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3034 in
                                         let t_kinding =
                                           let uu____3055 =
                                             let uu____3059 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3059,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3055 in
                                         let t_interp =
                                           let uu____3069 =
                                             let uu____3073 =
                                               let uu____3074 =
                                                 let uu____3080 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3080) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3074 in
                                             let uu____3092 =
                                               let uu____3094 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3094 in
                                             (uu____3073, uu____3092,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3069 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         (FStar_Util.smap_add env.cache
                                            tkey_hash
                                            (mk_cache_entry env tsym
                                               cvar_sorts t_decls);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3115 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3115 in
           let uu____3119 = encode_term_pred None k env ttm in
           (match uu____3119 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3127 =
                    let uu____3131 =
                      let uu____3132 =
                        let uu____3133 =
                          let uu____3134 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3134 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3133 in
                      varops.mk_unique uu____3132 in
                    (t_has_k, (Some "Uvar typing"), uu____3131) in
                  FStar_SMTEncoding_Term.Assume uu____3127 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3140 ->
           let uu____3150 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3150 with
            | (head1,args_e) ->
                let uu____3178 =
                  let uu____3186 =
                    let uu____3187 = FStar_Syntax_Subst.compress head1 in
                    uu____3187.FStar_Syntax_Syntax.n in
                  (uu____3186, args_e) in
                (match uu____3178 with
                 | (uu____3197,uu____3198) when head_redex env head1 ->
                     let uu____3209 = whnf env t in
                     encode_term uu____3209 env
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_),_::(v1,_)::
                    (v2,_)::[])
                   |(FStar_Syntax_Syntax.Tm_fvar fv,_::(v1,_)::(v2,_)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3283 = encode_term v1 env in
                     (match uu____3283 with
                      | (v11,decls1) ->
                          let uu____3290 = encode_term v2 env in
                          (match uu____3290 with
                           | (v21,decls2) ->
                               let uu____3297 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3297,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3299) ->
                     let e0 =
                       let uu____3313 =
                         let uu____3316 =
                           let uu____3317 =
                             let uu____3327 =
                               let uu____3333 = FStar_List.hd args_e in
                               [uu____3333] in
                             (head1, uu____3327) in
                           FStar_Syntax_Syntax.Tm_app uu____3317 in
                         FStar_Syntax_Syntax.mk uu____3316 in
                       uu____3313 None head1.FStar_Syntax_Syntax.pos in
                     ((let uu____3366 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3366
                       then
                         let uu____3367 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Trying to normalize %s\n"
                           uu____3367
                       else ());
                      (let e01 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Reify;
                           FStar_TypeChecker_Normalize.Eager_unfolding;
                           FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                           env.tcenv e0 in
                       (let uu____3371 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify") in
                        if uu____3371
                        then
                          let uu____3372 =
                            FStar_Syntax_Print.term_to_string e01 in
                          FStar_Util.print1 "Result of normalization %s\n"
                            uu____3372
                        else ());
                       (let e02 =
                          let uu____3375 =
                            let uu____3376 =
                              let uu____3377 =
                                FStar_Syntax_Subst.compress e01 in
                              uu____3377.FStar_Syntax_Syntax.n in
                            match uu____3376 with
                            | FStar_Syntax_Syntax.Tm_app uu____3380 -> false
                            | uu____3390 -> true in
                          if uu____3375
                          then e01
                          else
                            (let uu____3392 =
                               FStar_Syntax_Util.head_and_args e01 in
                             match uu____3392 with
                             | (head2,args) ->
                                 let uu____3418 =
                                   let uu____3419 =
                                     let uu____3420 =
                                       FStar_Syntax_Subst.compress head2 in
                                     uu____3420.FStar_Syntax_Syntax.n in
                                   match uu____3419 with
                                   | FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_reify ) -> true
                                   | uu____3423 -> false in
                                 if uu____3418
                                 then
                                   (match args with
                                    | x::[] -> Prims.fst x
                                    | uu____3439 ->
                                        failwith
                                          "Impossible : Reify applied to multiple arguments after normalization.")
                                 else e01) in
                        let e =
                          match args_e with
                          | uu____3447::[] -> e02
                          | uu____3460 ->
                              let uu____3466 =
                                let uu____3469 =
                                  let uu____3470 =
                                    let uu____3480 = FStar_List.tl args_e in
                                    (e02, uu____3480) in
                                  FStar_Syntax_Syntax.Tm_app uu____3470 in
                                FStar_Syntax_Syntax.mk uu____3469 in
                              uu____3466 None t0.FStar_Syntax_Syntax.pos in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3503),(arg,uu____3505)::[]) -> encode_term arg env
                 | uu____3523 ->
                     let uu____3531 = encode_args args_e env in
                     (match uu____3531 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3564 = encode_term head1 env in
                            match uu____3564 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3603 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3603 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3645  ->
                                                 fun uu____3646  ->
                                                   match (uu____3645,
                                                           uu____3646)
                                                   with
                                                   | ((bv,uu____3660),
                                                      (a,uu____3662)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3676 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3676
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3681 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3681 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3691 =
                                                   let uu____3695 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3700 =
                                                     let uu____3701 =
                                                       let uu____3702 =
                                                         let uu____3703 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3703 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3702 in
                                                     varops.mk_unique
                                                       uu____3701 in
                                                   (uu____3695,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3700) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3691 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3720 = lookup_free_var_sym env fv in
                            match uu____3720 with
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
                                 FStar_Syntax_Syntax.tk = _;
                                 FStar_Syntax_Syntax.pos = _;
                                 FStar_Syntax_Syntax.vars = _;_},_)
                              |FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                              ({
                                 FStar_Syntax_Syntax.n =
                                   FStar_Syntax_Syntax.Tm_fvar fv;
                                 FStar_Syntax_Syntax.tk = _;
                                 FStar_Syntax_Syntax.pos = _;
                                 FStar_Syntax_Syntax.vars = _;_},_)
                              |FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____3758 =
                                  let uu____3759 =
                                    let uu____3762 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3762 Prims.fst in
                                  FStar_All.pipe_right uu____3759 Prims.snd in
                                Some uu____3758
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3781,(FStar_Util.Inl t1,uu____3783),uu____3784)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3822,(FStar_Util.Inr c,uu____3824),uu____3825)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3863 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3883 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3883 in
                               let uu____3884 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3884 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                       ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = _;
                                          FStar_Syntax_Syntax.pos = _;
                                          FStar_Syntax_Syntax.vars = _;_},_)
                                       |FStar_Syntax_Syntax.Tm_fvar fv when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | uu____3909 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3954 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3954 with
            | (bs1,body1,opening) ->
                let fallback uu____3969 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3974 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3974, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3985 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3985
                  | FStar_Util.Inr (eff,uu____3987) ->
                      let uu____3993 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3993 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body = reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4038 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___152_4039 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___152_4039.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___152_4039.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___152_4039.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___152_4039.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___152_4039.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___152_4039.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___152_4039.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___152_4039.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___152_4039.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___152_4039.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___152_4039.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___152_4039.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___152_4039.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___152_4039.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___152_4039.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___152_4039.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___152_4039.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___152_4039.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___152_4039.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___152_4039.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___152_4039.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___152_4039.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___152_4039.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4038 FStar_Syntax_Syntax.U_unknown in
                        let uu____4040 =
                          let uu____4041 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4041 in
                        FStar_Util.Inl uu____4040
                    | FStar_Util.Inr (eff_name,uu____4048) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4079 =
                        let uu____4080 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4080 in
                      FStar_All.pipe_right uu____4079
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4092 =
                        let uu____4093 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4093 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4101 =
                          let uu____4102 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4102 in
                        FStar_All.pipe_right uu____4101
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4106 =
                             let uu____4107 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4107 in
                           FStar_All.pipe_right uu____4106
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4118 =
                         let uu____4119 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4119 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4118);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4134 =
                       (is_impure lc1) &&
                         (let uu____4135 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4135) in
                     if uu____4134
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4140 = encode_binders None bs1 env in
                        match uu____4140 with
                        | (vars,guards,envbody,decls,uu____4155) ->
                            let uu____4162 =
                              let uu____4170 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4170
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4162 with
                             | (lc2,body2) ->
                                 let uu____4195 = encode_term body2 envbody in
                                 (match uu____4195 with
                                  | (body3,decls') ->
                                      let uu____4202 =
                                        let uu____4207 = codomain_eff lc2 in
                                        match uu____4207 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4219 =
                                              encode_term tfun env in
                                            (match uu____4219 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4202 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4238 =
                                               let uu____4244 =
                                                 let uu____4245 =
                                                   let uu____4248 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4248, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4245 in
                                               ([], vars, uu____4244) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4238 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4256 =
                                                   let uu____4258 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4258 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4256 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4269 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4269 with
                                            | Some cache_entry ->
                                                let uu____4274 =
                                                  let uu____4275 =
                                                    let uu____4279 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4279) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4275 in
                                                let uu____4284 =
                                                  get_activation_facts
                                                    cache_entry in
                                                (uu____4274, uu____4284)
                                            | None  ->
                                                let uu____4287 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4287 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4294 =
                                                         let uu____4295 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4295 =
                                                           cache_size in
                                                       if uu____4294
                                                       then []
                                                       else
                                                         FStar_List.append
                                                           decls decls' in
                                                     (t1, decls1)
                                                 | None  ->
                                                     let cvar_sorts =
                                                       FStar_List.map
                                                         Prims.snd cvars1 in
                                                     let fsym =
                                                       let module_name =
                                                         env.current_module_name in
                                                       let fsym =
                                                         let uu____4306 =
                                                           let uu____4307 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4307 in
                                                         varops.mk_unique
                                                           uu____4306 in
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
                                                       let uu____4312 =
                                                         let uu____4316 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4316) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4312 in
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
                                                           let uu____4328 =
                                                             let uu____4329 =
                                                               let uu____4333
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4333,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____4329 in
                                                           [uu____4328] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4341 =
                                                         let uu____4345 =
                                                           let uu____4346 =
                                                             let uu____4352 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4352) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4346 in
                                                         (uu____4345,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Term.Assume
                                                         uu____4341 in
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
                                                     (FStar_Util.smap_add
                                                        env.cache tkey_hash
                                                        (mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4363,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4364;
                          FStar_Syntax_Syntax.lbunivs = uu____4365;
                          FStar_Syntax_Syntax.lbtyp = uu____4366;
                          FStar_Syntax_Syntax.lbeff = uu____4367;
                          FStar_Syntax_Syntax.lbdef = uu____4368;_}::uu____4369),uu____4370)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4388;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4390;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4406 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4419 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4419, [decl_e])))
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
              let uu____4461 = encode_term e1 env in
              match uu____4461 with
              | (ee1,decls1) ->
                  let uu____4468 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4468 with
                   | (xs,e21) ->
                       let uu____4482 = FStar_List.hd xs in
                       (match uu____4482 with
                        | (x1,uu____4490) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4492 = encode_body e21 env' in
                            (match uu____4492 with
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
            let uu____4514 =
              let uu____4518 =
                let uu____4519 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4519 in
              gen_term_var env uu____4518 in
            match uu____4514 with
            | (scrsym,scr',env1) ->
                let uu____4533 = encode_term e env1 in
                (match uu____4533 with
                 | (scr,decls) ->
                     let uu____4540 =
                       let encode_branch b uu____4556 =
                         match uu____4556 with
                         | (else_case,decls1) ->
                             let uu____4567 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4567 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4597  ->
                                       fun uu____4598  ->
                                         match (uu____4597, uu____4598) with
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
                                                       fun uu____4635  ->
                                                         match uu____4635
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4640 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4655 =
                                                     encode_term w1 env2 in
                                                   (match uu____4655 with
                                                    | (w2,decls21) ->
                                                        let uu____4663 =
                                                          let uu____4664 =
                                                            let uu____4667 =
                                                              let uu____4668
                                                                =
                                                                let uu____4671
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4671) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4668 in
                                                            (guard,
                                                              uu____4667) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4664 in
                                                        (uu____4663, decls21)) in
                                             (match uu____4640 with
                                              | (guard1,decls21) ->
                                                  let uu____4679 =
                                                    encode_br br env2 in
                                                  (match uu____4679 with
                                                   | (br1,decls3) ->
                                                       let uu____4687 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4687,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4540 with
                      | (match_tm,decls1) ->
                          let uu____4699 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4699, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4730 -> let uu____4731 = encode_one_pat env pat in [uu____4731]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4743 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4743
       then
         let uu____4744 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4744
       else ());
      (let uu____4746 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4746 with
       | (vars,pat_term) ->
           let uu____4756 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4779  ->
                     fun v1  ->
                       match uu____4779 with
                       | (env1,vars1) ->
                           let uu____4807 = gen_term_var env1 v1 in
                           (match uu____4807 with
                            | (xx,uu____4819,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4756 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4866 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4874 =
                        let uu____4877 = encode_const c in
                        (scrutinee, uu____4877) in
                      FStar_SMTEncoding_Util.mkEq uu____4874
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4896 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4896 with
                        | (uu____4900,uu____4901::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4903 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4924  ->
                                  match uu____4924 with
                                  | (arg,uu____4930) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4940 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4940)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4959 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4974 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4989 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5011  ->
                                  match uu____5011 with
                                  | (arg,uu____5020) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5030 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5030)) in
                      FStar_All.pipe_right uu____4989 FStar_List.flatten in
                let pat_term1 uu____5046 = encode_term pat_term env1 in
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
      let uu____5053 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5068  ->
                fun uu____5069  ->
                  match (uu____5068, uu____5069) with
                  | ((tms,decls),(t,uu____5089)) ->
                      let uu____5100 = encode_term t env in
                      (match uu____5100 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5053 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.term Prims.option ->
      FStar_Syntax_Syntax.typ ->
        env_t ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun induction_on  ->
    fun new_pats  ->
      fun t  ->
        fun env  ->
          let list_elements1 e =
            let uu____5138 = FStar_Syntax_Util.list_elements e in
            match uu____5138 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 []) in
          let one_pat p =
            let uu____5156 =
              let uu____5166 = FStar_Syntax_Util.unmeta p in
              FStar_All.pipe_right uu____5166 FStar_Syntax_Util.head_and_args in
            match uu____5156 with
            | (head1,args) ->
                let uu____5197 =
                  let uu____5205 =
                    let uu____5206 = FStar_Syntax_Util.un_uinst head1 in
                    uu____5206.FStar_Syntax_Syntax.n in
                  (uu____5205, args) in
                (match uu____5197 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5220,uu____5221)::(e,uu____5223)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5254)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5275 -> failwith "Unexpected pattern term") in
          let lemma_pats p =
            let elts = list_elements1 p in
            let smt_pat_or t1 =
              let uu____5308 =
                let uu____5318 = FStar_Syntax_Util.unmeta t1 in
                FStar_All.pipe_right uu____5318
                  FStar_Syntax_Util.head_and_args in
              match uu____5308 with
              | (head1,args) ->
                  let uu____5347 =
                    let uu____5355 =
                      let uu____5356 = FStar_Syntax_Util.un_uinst head1 in
                      uu____5356.FStar_Syntax_Syntax.n in
                    (uu____5355, args) in
                  (match uu____5347 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5369)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5389 -> None) in
            match elts with
            | t1::[] ->
                let uu____5407 = smt_pat_or t1 in
                (match uu____5407 with
                 | Some e ->
                     let uu____5423 = list_elements1 e in
                     FStar_All.pipe_right uu____5423
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5440 = list_elements1 branch1 in
                             FStar_All.pipe_right uu____5440
                               (FStar_List.map one_pat)))
                 | uu____5454 ->
                     let uu____5458 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat) in
                     [uu____5458])
            | uu____5489 ->
                let uu____5491 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat) in
                [uu____5491] in
          let uu____5522 =
            let uu____5538 =
              let uu____5539 = FStar_Syntax_Subst.compress t in
              uu____5539.FStar_Syntax_Syntax.n in
            match uu____5538 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5569 = FStar_Syntax_Subst.open_comp binders c in
                (match uu____5569 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5604;
                            FStar_Syntax_Syntax.effect_name = uu____5605;
                            FStar_Syntax_Syntax.result_typ = uu____5606;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5608)::(post,uu____5610)::(pats,uu____5612)::[];
                            FStar_Syntax_Syntax.flags = uu____5613;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats in
                          let uu____5647 = lemma_pats pats' in
                          (binders1, pre, post, uu____5647)
                      | uu____5666 -> failwith "impos"))
            | uu____5682 -> failwith "Impos" in
          match uu____5522 with
          | (binders,pre,post,patterns) ->
              let uu____5726 = encode_binders None binders env in
              (match uu____5726 with
               | (vars,guards,env1,decls,uu____5741) ->
                   let uu____5748 =
                     let uu____5755 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5786 =
                                 let uu____5791 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5807  ->
                                           match uu____5807 with
                                           | (t1,uu____5814) ->
                                               encode_term t1
                                                 (let uu___153_5817 = env1 in
                                                  {
                                                    bindings =
                                                      (uu___153_5817.bindings);
                                                    depth =
                                                      (uu___153_5817.depth);
                                                    tcenv =
                                                      (uu___153_5817.tcenv);
                                                    warn =
                                                      (uu___153_5817.warn);
                                                    cache =
                                                      (uu___153_5817.cache);
                                                    nolabels =
                                                      (uu___153_5817.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___153_5817.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___153_5817.current_module_name);
                                                    activate_current_sigelt_facts
                                                      =
                                                      (uu___153_5817.activate_current_sigelt_facts)
                                                  }))) in
                                 FStar_All.pipe_right uu____5791
                                   FStar_List.unzip in
                               match uu____5786 with
                               | (pats,decls1) -> (pats, decls1))) in
                     FStar_All.pipe_right uu____5755 FStar_List.unzip in
                   (match uu____5748 with
                    | (pats,decls') ->
                        let decls'1 = FStar_List.flatten decls' in
                        let pats1 =
                          match induction_on with
                          | None  -> pats
                          | Some e ->
                              (match vars with
                               | [] -> pats
                               | l::[] ->
                                   FStar_All.pipe_right pats
                                     (FStar_List.map
                                        (fun p  ->
                                           let uu____5881 =
                                             let uu____5882 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5882 e in
                                           uu____5881 :: p))
                               | uu____5883 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5912 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e in
                                                 uu____5912 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5920 =
                                           let uu____5921 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort) in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5921 tl1 in
                                         aux uu____5920 vars2
                                     | uu____5922 -> pats in
                                   let uu____5926 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort) in
                                   aux uu____5926 vars) in
                        let env2 =
                          let uu___154_5928 = env1 in
                          {
                            bindings = (uu___154_5928.bindings);
                            depth = (uu___154_5928.depth);
                            tcenv = (uu___154_5928.tcenv);
                            warn = (uu___154_5928.warn);
                            cache = (uu___154_5928.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___154_5928.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___154_5928.encode_non_total_function_typ);
                            current_module_name =
                              (uu___154_5928.current_module_name);
                            activate_current_sigelt_facts =
                              (uu___154_5928.activate_current_sigelt_facts)
                          } in
                        let uu____5929 =
                          let uu____5932 = FStar_Syntax_Util.unmeta pre in
                          encode_formula uu____5932 env2 in
                        (match uu____5929 with
                         | (pre1,decls'') ->
                             let uu____5937 =
                               let uu____5940 = FStar_Syntax_Util.unmeta post in
                               encode_formula uu____5940 env2 in
                             (match uu____5937 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls''')) in
                                  let uu____5947 =
                                    let uu____5948 =
                                      let uu____5954 =
                                        let uu____5955 =
                                          let uu____5958 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards) in
                                          (uu____5958, post1) in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5955 in
                                      (pats1, vars, uu____5954) in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5948 in
                                  (uu____5947, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5971 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5971
        then
          let uu____5972 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5973 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5972 uu____5973
        else () in
      let enc f r l =
        let uu____6000 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6013 = encode_term (Prims.fst x) env in
                 match uu____6013 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6000 with
        | (decls,args) ->
            let uu____6030 =
              let uu___155_6031 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___155_6031.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___155_6031.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6030, decls) in
      let const_op f r uu____6050 = let uu____6053 = f r in (uu____6053, []) in
      let un_op f l =
        let uu____6069 = FStar_List.hd l in FStar_All.pipe_left f uu____6069 in
      let bin_op f uu___126_6082 =
        match uu___126_6082 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6090 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6117 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6126  ->
                 match uu____6126 with
                 | (t,uu____6134) ->
                     let uu____6135 = encode_formula t env in
                     (match uu____6135 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6117 with
        | (decls,phis) ->
            let uu____6152 =
              let uu___156_6153 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___156_6153.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___156_6153.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6152, decls) in
      let eq_op r uu___127_6169 =
        match uu___127_6169 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6229 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6229 r [e1; e2]
        | l ->
            let uu____6249 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6249 r l in
      let mk_imp1 r uu___128_6268 =
        match uu___128_6268 with
        | (lhs,uu____6272)::(rhs,uu____6274)::[] ->
            let uu____6295 = encode_formula rhs env in
            (match uu____6295 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6304) ->
                      (l1, decls1)
                  | uu____6307 ->
                      let uu____6308 = encode_formula lhs env in
                      (match uu____6308 with
                       | (l2,decls2) ->
                           let uu____6315 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6315, (FStar_List.append decls1 decls2)))))
        | uu____6317 -> failwith "impossible" in
      let mk_ite r uu___129_6332 =
        match uu___129_6332 with
        | (guard,uu____6336)::(_then,uu____6338)::(_else,uu____6340)::[] ->
            let uu____6369 = encode_formula guard env in
            (match uu____6369 with
             | (g,decls1) ->
                 let uu____6376 = encode_formula _then env in
                 (match uu____6376 with
                  | (t,decls2) ->
                      let uu____6383 = encode_formula _else env in
                      (match uu____6383 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6392 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6411 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6411 in
      let connectives =
        let uu____6423 =
          let uu____6432 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6432) in
        let uu____6445 =
          let uu____6455 =
            let uu____6464 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6464) in
          let uu____6477 =
            let uu____6487 =
              let uu____6497 =
                let uu____6506 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6506) in
              let uu____6519 =
                let uu____6529 =
                  let uu____6539 =
                    let uu____6548 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6548) in
                  [uu____6539;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6529 in
              uu____6497 :: uu____6519 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6487 in
          uu____6455 :: uu____6477 in
        uu____6423 :: uu____6445 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6710 = encode_formula phi' env in
            (match uu____6710 with
             | (phi2,decls) ->
                 let uu____6717 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6717, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6718 ->
            let uu____6723 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6723 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6752 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6752 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6760;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6762;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6778 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6778 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6810::(x,uu____6812)::(t,uu____6814)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6848 = encode_term x env in
                 (match uu____6848 with
                  | (x1,decls) ->
                      let uu____6855 = encode_term t env in
                      (match uu____6855 with
                       | (t1,decls') ->
                           let uu____6862 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6862, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6866)::(msg,uu____6868)::(phi2,uu____6870)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6904 =
                   let uu____6907 =
                     let uu____6908 = FStar_Syntax_Subst.compress r in
                     uu____6908.FStar_Syntax_Syntax.n in
                   let uu____6911 =
                     let uu____6912 = FStar_Syntax_Subst.compress msg in
                     uu____6912.FStar_Syntax_Syntax.n in
                   (uu____6907, uu____6911) in
                 (match uu____6904 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6919))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6935 -> fallback phi2)
             | uu____6938 when head_redex env head2 ->
                 let uu____6946 = whnf env phi1 in
                 encode_formula uu____6946 env
             | uu____6947 ->
                 let uu____6955 = encode_term phi1 env in
                 (match uu____6955 with
                  | (tt,decls) ->
                      let uu____6962 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___157_6963 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___157_6963.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___157_6963.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6962, decls)))
        | uu____6966 ->
            let uu____6967 = encode_term phi1 env in
            (match uu____6967 with
             | (tt,decls) ->
                 let uu____6974 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___158_6975 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___158_6975.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___158_6975.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6974, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7002 = encode_binders None bs env1 in
        match uu____7002 with
        | (vars,guards,env2,decls,uu____7024) ->
            let uu____7031 =
              let uu____7038 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7061 =
                          let uu____7066 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7080  ->
                                    match uu____7080 with
                                    | (t,uu____7086) ->
                                        encode_term t
                                          (let uu___159_7087 = env2 in
                                           {
                                             bindings =
                                               (uu___159_7087.bindings);
                                             depth = (uu___159_7087.depth);
                                             tcenv = (uu___159_7087.tcenv);
                                             warn = (uu___159_7087.warn);
                                             cache = (uu___159_7087.cache);
                                             nolabels =
                                               (uu___159_7087.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___159_7087.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___159_7087.current_module_name);
                                             activate_current_sigelt_facts =
                                               (uu___159_7087.activate_current_sigelt_facts)
                                           }))) in
                          FStar_All.pipe_right uu____7066 FStar_List.unzip in
                        match uu____7061 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7038 FStar_List.unzip in
            (match uu____7031 with
             | (pats,decls') ->
                 let uu____7139 = encode_formula body env2 in
                 (match uu____7139 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7158;
                             FStar_SMTEncoding_Term.rng = uu____7159;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7167 -> guards in
                      let uu____7170 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7170, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7204  ->
                   match uu____7204 with
                   | (x,uu____7208) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7214 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7220 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7220) uu____7214 tl1 in
             let uu____7222 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7234  ->
                       match uu____7234 with
                       | (b,uu____7238) ->
                           let uu____7239 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7239)) in
             (match uu____7222 with
              | None  -> ()
              | Some (x,uu____7243) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7253 =
                    let uu____7254 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7254 in
                  FStar_Errors.warn pos uu____7253) in
       let uu____7255 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7255 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7261 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7297  ->
                     match uu____7297 with
                     | (l,uu____7307) -> FStar_Ident.lid_equals op l)) in
           (match uu____7261 with
            | None  -> fallback phi1
            | Some (uu____7330,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7359 = encode_q_body env vars pats body in
             match uu____7359 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7385 =
                     let uu____7391 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7391) in
                   FStar_SMTEncoding_Term.mkForall uu____7385
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7403 = encode_q_body env vars pats body in
             match uu____7403 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7428 =
                   let uu____7429 =
                     let uu____7435 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7435) in
                   FStar_SMTEncoding_Term.mkExists uu____7429
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7428, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7484 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7484 with
  | (asym,a) ->
      let uu____7489 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7489 with
       | (xsym,x) ->
           let uu____7494 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7494 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7524 =
                      let uu____7530 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7530, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7524 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7545 =
                      let uu____7549 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7549) in
                    FStar_SMTEncoding_Util.mkApp uu____7545 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7557 =
                    let uu____7559 =
                      let uu____7561 =
                        let uu____7563 =
                          let uu____7564 =
                            let uu____7568 =
                              let uu____7569 =
                                let uu____7575 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7575) in
                              FStar_SMTEncoding_Util.mkForall uu____7569 in
                            (uu____7568, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Term.Assume uu____7564 in
                        let uu____7584 =
                          let uu____7586 =
                            let uu____7587 =
                              let uu____7591 =
                                let uu____7592 =
                                  let uu____7598 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7598) in
                                FStar_SMTEncoding_Util.mkForall uu____7592 in
                              (uu____7591,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Term.Assume uu____7587 in
                          [uu____7586] in
                        uu____7563 :: uu____7584 in
                      xtok_decl :: uu____7561 in
                    xname_decl :: uu____7559 in
                  (xtok1, uu____7557) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7647 =
                    let uu____7655 =
                      let uu____7661 =
                        let uu____7662 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7662 in
                      quant axy uu____7661 in
                    (FStar_Syntax_Const.op_Eq, uu____7655) in
                  let uu____7668 =
                    let uu____7677 =
                      let uu____7685 =
                        let uu____7691 =
                          let uu____7692 =
                            let uu____7693 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7693 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7692 in
                        quant axy uu____7691 in
                      (FStar_Syntax_Const.op_notEq, uu____7685) in
                    let uu____7699 =
                      let uu____7708 =
                        let uu____7716 =
                          let uu____7722 =
                            let uu____7723 =
                              let uu____7724 =
                                let uu____7727 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7728 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7727, uu____7728) in
                              FStar_SMTEncoding_Util.mkLT uu____7724 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7723 in
                          quant xy uu____7722 in
                        (FStar_Syntax_Const.op_LT, uu____7716) in
                      let uu____7734 =
                        let uu____7743 =
                          let uu____7751 =
                            let uu____7757 =
                              let uu____7758 =
                                let uu____7759 =
                                  let uu____7762 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7763 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7762, uu____7763) in
                                FStar_SMTEncoding_Util.mkLTE uu____7759 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7758 in
                            quant xy uu____7757 in
                          (FStar_Syntax_Const.op_LTE, uu____7751) in
                        let uu____7769 =
                          let uu____7778 =
                            let uu____7786 =
                              let uu____7792 =
                                let uu____7793 =
                                  let uu____7794 =
                                    let uu____7797 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7798 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7797, uu____7798) in
                                  FStar_SMTEncoding_Util.mkGT uu____7794 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7793 in
                              quant xy uu____7792 in
                            (FStar_Syntax_Const.op_GT, uu____7786) in
                          let uu____7804 =
                            let uu____7813 =
                              let uu____7821 =
                                let uu____7827 =
                                  let uu____7828 =
                                    let uu____7829 =
                                      let uu____7832 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7833 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7832, uu____7833) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7829 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7828 in
                                quant xy uu____7827 in
                              (FStar_Syntax_Const.op_GTE, uu____7821) in
                            let uu____7839 =
                              let uu____7848 =
                                let uu____7856 =
                                  let uu____7862 =
                                    let uu____7863 =
                                      let uu____7864 =
                                        let uu____7867 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7868 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7867, uu____7868) in
                                      FStar_SMTEncoding_Util.mkSub uu____7864 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7863 in
                                  quant xy uu____7862 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7856) in
                              let uu____7874 =
                                let uu____7883 =
                                  let uu____7891 =
                                    let uu____7897 =
                                      let uu____7898 =
                                        let uu____7899 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7899 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7898 in
                                    quant qx uu____7897 in
                                  (FStar_Syntax_Const.op_Minus, uu____7891) in
                                let uu____7905 =
                                  let uu____7914 =
                                    let uu____7922 =
                                      let uu____7928 =
                                        let uu____7929 =
                                          let uu____7930 =
                                            let uu____7933 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7934 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7933, uu____7934) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7930 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7929 in
                                      quant xy uu____7928 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7922) in
                                  let uu____7940 =
                                    let uu____7949 =
                                      let uu____7957 =
                                        let uu____7963 =
                                          let uu____7964 =
                                            let uu____7965 =
                                              let uu____7968 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7969 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7968, uu____7969) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7965 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7964 in
                                        quant xy uu____7963 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7957) in
                                    let uu____7975 =
                                      let uu____7984 =
                                        let uu____7992 =
                                          let uu____7998 =
                                            let uu____7999 =
                                              let uu____8000 =
                                                let uu____8003 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8004 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8003, uu____8004) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8000 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7999 in
                                          quant xy uu____7998 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7992) in
                                      let uu____8010 =
                                        let uu____8019 =
                                          let uu____8027 =
                                            let uu____8033 =
                                              let uu____8034 =
                                                let uu____8035 =
                                                  let uu____8038 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8039 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8038, uu____8039) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8035 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8034 in
                                            quant xy uu____8033 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8027) in
                                        let uu____8045 =
                                          let uu____8054 =
                                            let uu____8062 =
                                              let uu____8068 =
                                                let uu____8069 =
                                                  let uu____8070 =
                                                    let uu____8073 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8074 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8073, uu____8074) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8070 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8069 in
                                              quant xy uu____8068 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8062) in
                                          let uu____8080 =
                                            let uu____8089 =
                                              let uu____8097 =
                                                let uu____8103 =
                                                  let uu____8104 =
                                                    let uu____8105 =
                                                      let uu____8108 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8109 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8108,
                                                        uu____8109) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8105 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8104 in
                                                quant xy uu____8103 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8097) in
                                            let uu____8115 =
                                              let uu____8124 =
                                                let uu____8132 =
                                                  let uu____8138 =
                                                    let uu____8139 =
                                                      let uu____8140 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8140 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8139 in
                                                  quant qx uu____8138 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8132) in
                                              [uu____8124] in
                                            uu____8089 :: uu____8115 in
                                          uu____8054 :: uu____8080 in
                                        uu____8019 :: uu____8045 in
                                      uu____7984 :: uu____8010 in
                                    uu____7949 :: uu____7975 in
                                  uu____7914 :: uu____7940 in
                                uu____7883 :: uu____7905 in
                              uu____7848 :: uu____7874 in
                            uu____7813 :: uu____7839 in
                          uu____7778 :: uu____7804 in
                        uu____7743 :: uu____7769 in
                      uu____7708 :: uu____7734 in
                    uu____7677 :: uu____7699 in
                  uu____7647 :: uu____7668 in
                let mk1 l v1 =
                  let uu____8268 =
                    let uu____8273 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8305  ->
                              match uu____8305 with
                              | (l',uu____8314) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8273
                      (FStar_Option.map
                         (fun uu____8347  ->
                            match uu____8347 with | (uu____8358,b) -> b v1)) in
                  FStar_All.pipe_right uu____8268 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8399  ->
                          match uu____8399 with
                          | (l',uu____8408) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8434 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8434 with
        | (xxsym,xx) ->
            let uu____8439 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8439 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8447 =
                   let uu____8451 =
                     let uu____8452 =
                       let uu____8458 =
                         let uu____8459 =
                           let uu____8462 =
                             let uu____8463 =
                               let uu____8466 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8466) in
                             FStar_SMTEncoding_Util.mkEq uu____8463 in
                           (xx_has_type, uu____8462) in
                         FStar_SMTEncoding_Util.mkImp uu____8459 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8458) in
                     FStar_SMTEncoding_Util.mkForall uu____8452 in
                   let uu____8479 =
                     let uu____8480 =
                       let uu____8481 =
                         let uu____8482 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8482 in
                       Prims.strcat module_name uu____8481 in
                     varops.mk_unique uu____8480 in
                   (uu____8451, (Some "pretyping"), uu____8479) in
                 FStar_SMTEncoding_Term.Assume uu____8447)
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
    let uu____8512 =
      let uu____8513 =
        let uu____8517 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8517, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Term.Assume uu____8513 in
    let uu____8519 =
      let uu____8521 =
        let uu____8522 =
          let uu____8526 =
            let uu____8527 =
              let uu____8533 =
                let uu____8534 =
                  let uu____8537 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8537) in
                FStar_SMTEncoding_Util.mkImp uu____8534 in
              ([[typing_pred]], [xx], uu____8533) in
            mkForall_fuel uu____8527 in
          (uu____8526, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8522 in
      [uu____8521] in
    uu____8512 :: uu____8519 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8565 =
      let uu____8566 =
        let uu____8570 =
          let uu____8571 =
            let uu____8577 =
              let uu____8580 =
                let uu____8582 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8582] in
              [uu____8580] in
            let uu____8585 =
              let uu____8586 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8586 tt in
            (uu____8577, [bb], uu____8585) in
          FStar_SMTEncoding_Util.mkForall uu____8571 in
        (uu____8570, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Term.Assume uu____8566 in
    let uu____8597 =
      let uu____8599 =
        let uu____8600 =
          let uu____8604 =
            let uu____8605 =
              let uu____8611 =
                let uu____8612 =
                  let uu____8615 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8615) in
                FStar_SMTEncoding_Util.mkImp uu____8612 in
              ([[typing_pred]], [xx], uu____8611) in
            mkForall_fuel uu____8605 in
          (uu____8604, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8600 in
      [uu____8599] in
    uu____8565 :: uu____8597 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8649 =
        let uu____8650 =
          let uu____8654 =
            let uu____8656 =
              let uu____8658 =
                let uu____8660 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8661 =
                  let uu____8663 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8663] in
                uu____8660 :: uu____8661 in
              tt :: uu____8658 in
            tt :: uu____8656 in
          ("Prims.Precedes", uu____8654) in
        FStar_SMTEncoding_Util.mkApp uu____8650 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8649 in
    let precedes_y_x =
      let uu____8666 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8666 in
    let uu____8668 =
      let uu____8669 =
        let uu____8673 =
          let uu____8674 =
            let uu____8680 =
              let uu____8683 =
                let uu____8685 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8685] in
              [uu____8683] in
            let uu____8688 =
              let uu____8689 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8689 tt in
            (uu____8680, [bb], uu____8688) in
          FStar_SMTEncoding_Util.mkForall uu____8674 in
        (uu____8673, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Term.Assume uu____8669 in
    let uu____8700 =
      let uu____8702 =
        let uu____8703 =
          let uu____8707 =
            let uu____8708 =
              let uu____8714 =
                let uu____8715 =
                  let uu____8718 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8718) in
                FStar_SMTEncoding_Util.mkImp uu____8715 in
              ([[typing_pred]], [xx], uu____8714) in
            mkForall_fuel uu____8708 in
          (uu____8707, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8703 in
      let uu____8731 =
        let uu____8733 =
          let uu____8734 =
            let uu____8738 =
              let uu____8739 =
                let uu____8745 =
                  let uu____8746 =
                    let uu____8749 =
                      let uu____8750 =
                        let uu____8752 =
                          let uu____8754 =
                            let uu____8756 =
                              let uu____8757 =
                                let uu____8760 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8761 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8760, uu____8761) in
                              FStar_SMTEncoding_Util.mkGT uu____8757 in
                            let uu____8762 =
                              let uu____8764 =
                                let uu____8765 =
                                  let uu____8768 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8769 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8768, uu____8769) in
                                FStar_SMTEncoding_Util.mkGTE uu____8765 in
                              let uu____8770 =
                                let uu____8772 =
                                  let uu____8773 =
                                    let uu____8776 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8777 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8776, uu____8777) in
                                  FStar_SMTEncoding_Util.mkLT uu____8773 in
                                [uu____8772] in
                              uu____8764 :: uu____8770 in
                            uu____8756 :: uu____8762 in
                          typing_pred_y :: uu____8754 in
                        typing_pred :: uu____8752 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8750 in
                    (uu____8749, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8746 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8745) in
              mkForall_fuel uu____8739 in
            (uu____8738, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Term.Assume uu____8734 in
        [uu____8733] in
      uu____8702 :: uu____8731 in
    uu____8668 :: uu____8700 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8807 =
      let uu____8808 =
        let uu____8812 =
          let uu____8813 =
            let uu____8819 =
              let uu____8822 =
                let uu____8824 = FStar_SMTEncoding_Term.boxString b in
                [uu____8824] in
              [uu____8822] in
            let uu____8827 =
              let uu____8828 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8828 tt in
            (uu____8819, [bb], uu____8827) in
          FStar_SMTEncoding_Util.mkForall uu____8813 in
        (uu____8812, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Term.Assume uu____8808 in
    let uu____8839 =
      let uu____8841 =
        let uu____8842 =
          let uu____8846 =
            let uu____8847 =
              let uu____8853 =
                let uu____8854 =
                  let uu____8857 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8857) in
                FStar_SMTEncoding_Util.mkImp uu____8854 in
              ([[typing_pred]], [xx], uu____8853) in
            mkForall_fuel uu____8847 in
          (uu____8846, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8842 in
      [uu____8841] in
    uu____8807 :: uu____8839 in
  let mk_ref1 env reft_name uu____8879 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8890 =
        let uu____8894 =
          let uu____8896 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8896] in
        (reft_name, uu____8894) in
      FStar_SMTEncoding_Util.mkApp uu____8890 in
    let refb =
      let uu____8899 =
        let uu____8903 =
          let uu____8905 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8905] in
        (reft_name, uu____8903) in
      FStar_SMTEncoding_Util.mkApp uu____8899 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8909 =
      let uu____8910 =
        let uu____8914 =
          let uu____8915 =
            let uu____8921 =
              let uu____8922 =
                let uu____8925 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8925) in
              FStar_SMTEncoding_Util.mkImp uu____8922 in
            ([[typing_pred]], [xx; aa], uu____8921) in
          mkForall_fuel uu____8915 in
        (uu____8914, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Term.Assume uu____8910 in
    [uu____8909] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8965 =
      let uu____8966 =
        let uu____8970 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8970, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Term.Assume uu____8966 in
    [uu____8965] in
  let mk_and_interp env conj uu____8981 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8998 =
      let uu____8999 =
        let uu____9003 =
          let uu____9004 =
            let uu____9010 =
              let uu____9011 =
                let uu____9014 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9014, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9011 in
            ([[l_and_a_b]], [aa; bb], uu____9010) in
          FStar_SMTEncoding_Util.mkForall uu____9004 in
        (uu____9003, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Term.Assume uu____8999 in
    [uu____8998] in
  let mk_or_interp env disj uu____9038 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9055 =
      let uu____9056 =
        let uu____9060 =
          let uu____9061 =
            let uu____9067 =
              let uu____9068 =
                let uu____9071 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9071, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9068 in
            ([[l_or_a_b]], [aa; bb], uu____9067) in
          FStar_SMTEncoding_Util.mkForall uu____9061 in
        (uu____9060, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Term.Assume uu____9056 in
    [uu____9055] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9112 =
      let uu____9113 =
        let uu____9117 =
          let uu____9118 =
            let uu____9124 =
              let uu____9125 =
                let uu____9128 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9128, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9125 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9124) in
          FStar_SMTEncoding_Util.mkForall uu____9118 in
        (uu____9117, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Term.Assume uu____9113 in
    [uu____9112] in
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
    let uu____9175 =
      let uu____9176 =
        let uu____9180 =
          let uu____9181 =
            let uu____9187 =
              let uu____9188 =
                let uu____9191 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9191, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9188 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9187) in
          FStar_SMTEncoding_Util.mkForall uu____9181 in
        (uu____9180, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Term.Assume uu____9176 in
    [uu____9175] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9236 =
      let uu____9237 =
        let uu____9241 =
          let uu____9242 =
            let uu____9248 =
              let uu____9249 =
                let uu____9252 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9252, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9249 in
            ([[l_imp_a_b]], [aa; bb], uu____9248) in
          FStar_SMTEncoding_Util.mkForall uu____9242 in
        (uu____9241, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Term.Assume uu____9237 in
    [uu____9236] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9293 =
      let uu____9294 =
        let uu____9298 =
          let uu____9299 =
            let uu____9305 =
              let uu____9306 =
                let uu____9309 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9309, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9306 in
            ([[l_iff_a_b]], [aa; bb], uu____9305) in
          FStar_SMTEncoding_Util.mkForall uu____9299 in
        (uu____9298, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Term.Assume uu____9294 in
    [uu____9293] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9343 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9343 in
    let uu____9345 =
      let uu____9346 =
        let uu____9350 =
          let uu____9351 =
            let uu____9357 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9357) in
          FStar_SMTEncoding_Util.mkForall uu____9351 in
        (uu____9350, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Term.Assume uu____9346 in
    [uu____9345] in
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
      let uu____9397 =
        let uu____9401 =
          let uu____9403 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9403] in
        ("Valid", uu____9401) in
      FStar_SMTEncoding_Util.mkApp uu____9397 in
    let uu____9405 =
      let uu____9406 =
        let uu____9410 =
          let uu____9411 =
            let uu____9417 =
              let uu____9418 =
                let uu____9421 =
                  let uu____9422 =
                    let uu____9428 =
                      let uu____9431 =
                        let uu____9433 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9433] in
                      [uu____9431] in
                    let uu____9436 =
                      let uu____9437 =
                        let uu____9440 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9440, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9437 in
                    (uu____9428, [xx1], uu____9436) in
                  FStar_SMTEncoding_Util.mkForall uu____9422 in
                (uu____9421, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9418 in
            ([[l_forall_a_b]], [aa; bb], uu____9417) in
          FStar_SMTEncoding_Util.mkForall uu____9411 in
        (uu____9410, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Term.Assume uu____9406 in
    [uu____9405] in
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
      let uu____9491 =
        let uu____9495 =
          let uu____9497 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9497] in
        ("Valid", uu____9495) in
      FStar_SMTEncoding_Util.mkApp uu____9491 in
    let uu____9499 =
      let uu____9500 =
        let uu____9504 =
          let uu____9505 =
            let uu____9511 =
              let uu____9512 =
                let uu____9515 =
                  let uu____9516 =
                    let uu____9522 =
                      let uu____9525 =
                        let uu____9527 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9527] in
                      [uu____9525] in
                    let uu____9530 =
                      let uu____9531 =
                        let uu____9534 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9534, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9531 in
                    (uu____9522, [xx1], uu____9530) in
                  FStar_SMTEncoding_Util.mkExists uu____9516 in
                (uu____9515, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9512 in
            ([[l_exists_a_b]], [aa; bb], uu____9511) in
          FStar_SMTEncoding_Util.mkForall uu____9505 in
        (uu____9504, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Term.Assume uu____9500 in
    [uu____9499] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9570 =
      let uu____9571 =
        let uu____9575 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9576 = varops.mk_unique "typing_range_const" in
        (uu____9575, (Some "Range_const typing"), uu____9576) in
      FStar_SMTEncoding_Term.Assume uu____9571 in
    [uu____9570] in
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
          let uu____9838 =
            FStar_Util.find_opt
              (fun uu____9856  ->
                 match uu____9856 with
                 | (l,uu____9866) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9838 with
          | None  -> []
          | Some (uu____9888,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9925 = encode_function_type_as_formula None None t env in
        match uu____9925 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Term.Assume
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
            let uu____9957 =
              (let uu____9958 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____9958) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____9957
            then
              let uu____9962 = new_term_constant_and_tok_from_lid env lid in
              match uu____9962 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____9974 =
                      let uu____9975 = FStar_Syntax_Subst.compress t_norm in
                      uu____9975.FStar_Syntax_Syntax.n in
                    match uu____9974 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9980) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____9997  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10000 -> [] in
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
              (let uu____10009 = prims.is lid in
               if uu____10009
               then
                 let vname = varops.new_fvar lid in
                 let uu____10014 = prims.mk lid vname in
                 match uu____10014 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10029 =
                    let uu____10035 = curried_arrow_formals_comp t_norm in
                    match uu____10035 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10046 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10046
                          then
                            let uu____10047 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___160_10048 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___160_10048.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___160_10048.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___160_10048.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___160_10048.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___160_10048.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___160_10048.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___160_10048.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___160_10048.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___160_10048.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___160_10048.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___160_10048.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___160_10048.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___160_10048.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___160_10048.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___160_10048.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___160_10048.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___160_10048.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___160_10048.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___160_10048.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___160_10048.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___160_10048.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___160_10048.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___160_10048.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10047
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10055 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10055)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10029 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10082 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10082 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10095 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___130_10119  ->
                                     match uu___130_10119 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10122 =
                                           FStar_Util.prefix vars in
                                         (match uu____10122 with
                                          | (uu____10133,(xxsym,uu____10135))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10145 =
                                                let uu____10146 =
                                                  let uu____10150 =
                                                    let uu____10151 =
                                                      let uu____10157 =
                                                        let uu____10158 =
                                                          let uu____10161 =
                                                            let uu____10162 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10162 in
                                                          (vapp, uu____10161) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10158 in
                                                      ([[vapp]], vars,
                                                        uu____10157) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10151 in
                                                  (uu____10150,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10146 in
                                              [uu____10145])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10173 =
                                           FStar_Util.prefix vars in
                                         (match uu____10173 with
                                          | (uu____10184,(xxsym,uu____10186))
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
                                              let uu____10200 =
                                                let uu____10201 =
                                                  let uu____10205 =
                                                    let uu____10206 =
                                                      let uu____10212 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10212) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10206 in
                                                  (uu____10205,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10201 in
                                              [uu____10200])
                                     | uu____10221 -> [])) in
                           let uu____10222 = encode_binders None formals env1 in
                           (match uu____10222 with
                            | (vars,guards,env',decls1,uu____10238) ->
                                let uu____10245 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10250 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10250, decls1)
                                  | Some p ->
                                      let uu____10252 = encode_formula p env' in
                                      (match uu____10252 with
                                       | (g,ds) ->
                                           let uu____10259 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10259,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10245 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10268 =
                                         let uu____10272 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10272) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10268 in
                                     let uu____10277 =
                                       let vname_decl =
                                         let uu____10282 =
                                           let uu____10288 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10293  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10288,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10282 in
                                       let uu____10298 =
                                         let env2 =
                                           let uu___161_10302 = env1 in
                                           {
                                             bindings =
                                               (uu___161_10302.bindings);
                                             depth = (uu___161_10302.depth);
                                             tcenv = (uu___161_10302.tcenv);
                                             warn = (uu___161_10302.warn);
                                             cache = (uu___161_10302.cache);
                                             nolabels =
                                               (uu___161_10302.nolabels);
                                             use_zfuel_name =
                                               (uu___161_10302.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___161_10302.current_module_name);
                                             activate_current_sigelt_facts =
                                               (uu___161_10302.activate_current_sigelt_facts)
                                           } in
                                         let uu____10303 =
                                           let uu____10304 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10304 in
                                         if uu____10303
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10298 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10314::uu____10315 ->
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
                                                   let uu____10338 =
                                                     let uu____10344 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10344) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10338 in
                                                 FStar_SMTEncoding_Term.Assume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10358 ->
                                                 FStar_SMTEncoding_Term.Assume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10360 =
                                             match formals with
                                             | [] ->
                                                 let uu____10369 =
                                                   let uu____10370 =
                                                     let uu____10372 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10372 in
                                                   push_free_var env1 lid
                                                     vname uu____10370 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10369)
                                             | uu____10375 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10380 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10380 in
                                                 let name_tok_corr =
                                                   let uu____10382 =
                                                     let uu____10386 =
                                                       let uu____10387 =
                                                         let uu____10393 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10393) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10387 in
                                                     (uu____10386,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Term.Assume
                                                     uu____10382 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10360 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10277 with
                                      | (decls2,env2) ->
                                          let uu____10417 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10422 =
                                              encode_term res_t1 env' in
                                            match uu____10422 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10430 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10430,
                                                  decls) in
                                          (match uu____10417 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10438 =
                                                   let uu____10442 =
                                                     let uu____10443 =
                                                       let uu____10449 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10449) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10443 in
                                                   (uu____10442,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____10438 in
                                               let freshness =
                                                 let uu____10458 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10458
                                                 then
                                                   let uu____10461 =
                                                     let uu____10462 =
                                                       let uu____10468 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10474 =
                                                         varops.next_id () in
                                                       (vname, uu____10468,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10474) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10462 in
                                                   let uu____10476 =
                                                     let uu____10478 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10478] in
                                                   uu____10461 :: uu____10476
                                                 else [] in
                                               let g =
                                                 let uu____10482 =
                                                   let uu____10484 =
                                                     let uu____10486 =
                                                       let uu____10488 =
                                                         let uu____10490 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10490 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10488 in
                                                     FStar_List.append decls3
                                                       uu____10486 in
                                                   FStar_List.append decls2
                                                     uu____10484 in
                                                 FStar_List.append decls11
                                                   uu____10482 in
                                               (g, env2))))))))
let declare_top_level_let:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string* FStar_SMTEncoding_Term.term Prims.option)*
            FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____10512 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10512 with
          | None  ->
              let uu____10535 = encode_free_var env x t t_norm [] in
              (match uu____10535 with
               | (decls,env1) ->
                   let uu____10550 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10550 with
                    | (n1,x',uu____10569) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10581) -> ((n1, x1), [], env)
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
          let uu____10614 = encode_free_var env lid t tt quals in
          match uu____10614 with
          | (decls,env1) ->
              let uu____10625 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10625
              then
                let uu____10629 =
                  let uu____10631 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10631 in
                (uu____10629, env1)
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
             (fun uu____10659  ->
                fun lb  ->
                  match uu____10659 with
                  | (decls,env1) ->
                      let uu____10671 =
                        let uu____10675 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10675
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10671 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10689 = FStar_Syntax_Util.head_and_args t in
    match uu____10689 with
    | (hd1,args) ->
        let uu____10715 =
          let uu____10716 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10716.FStar_Syntax_Syntax.n in
        (match uu____10715 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10720,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10733 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10748  ->
      fun quals  ->
        match uu____10748 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10797 = FStar_Util.first_N nbinders formals in
              match uu____10797 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10837  ->
                         fun uu____10838  ->
                           match (uu____10837, uu____10838) with
                           | ((formal,uu____10848),(binder,uu____10850)) ->
                               let uu____10855 =
                                 let uu____10860 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10860) in
                               FStar_Syntax_Syntax.NT uu____10855) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10865 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10879  ->
                              match uu____10879 with
                              | (x,i) ->
                                  let uu____10886 =
                                    let uu___162_10887 = x in
                                    let uu____10888 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___162_10887.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___162_10887.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10888
                                    } in
                                  (uu____10886, i))) in
                    FStar_All.pipe_right uu____10865
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10900 =
                      let uu____10902 =
                        let uu____10903 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10903.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10902 in
                    let uu____10907 =
                      let uu____10908 = FStar_Syntax_Subst.compress body in
                      let uu____10909 =
                        let uu____10910 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10910 in
                      FStar_Syntax_Syntax.extend_app_n uu____10908
                        uu____10909 in
                    uu____10907 uu____10900 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10952 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10952
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___163_10953 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___163_10953.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___163_10953.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___163_10953.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___163_10953.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___163_10953.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___163_10953.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___163_10953.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___163_10953.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___163_10953.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___163_10953.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___163_10953.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___163_10953.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___163_10953.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___163_10953.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___163_10953.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___163_10953.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___163_10953.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___163_10953.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___163_10953.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___163_10953.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___163_10953.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___163_10953.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___163_10953.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____10974 = FStar_Syntax_Util.abs_formals e in
                match uu____10974 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11023::uu____11024 ->
                         let uu____11032 =
                           let uu____11033 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11033.FStar_Syntax_Syntax.n in
                         (match uu____11032 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11060 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11060 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11086 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11086
                                   then
                                     let uu____11104 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11104 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11150  ->
                                                   fun uu____11151  ->
                                                     match (uu____11150,
                                                             uu____11151)
                                                     with
                                                     | ((x,uu____11161),
                                                        (b,uu____11163)) ->
                                                         let uu____11168 =
                                                           let uu____11173 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11173) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11168)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11175 =
                                            let uu____11186 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11186) in
                                          (uu____11175, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11221 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11221 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11273) ->
                              let uu____11278 =
                                let uu____11289 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11289 in
                              (uu____11278, true)
                          | uu____11322 when Prims.op_Negation norm1 ->
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
                          | uu____11324 ->
                              let uu____11325 =
                                let uu____11326 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11327 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11326
                                  uu____11327 in
                              failwith uu____11325)
                     | uu____11340 ->
                         let uu____11341 =
                           let uu____11342 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11342.FStar_Syntax_Syntax.n in
                         (match uu____11341 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11369 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11369 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11387 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11387 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11435 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11463 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11463
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11470 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11511  ->
                            fun lb  ->
                              match uu____11511 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11562 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11562
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11565 =
                                      let uu____11573 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11573
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11565 with
                                    | (tok,decl,env2) ->
                                        let uu____11598 =
                                          let uu____11605 =
                                            let uu____11611 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11611, tok) in
                                          uu____11605 :: toks in
                                        (uu____11598, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11470 with
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
                        | uu____11713 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11718 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11718 vars)
                            else
                              (let uu____11720 =
                                 let uu____11724 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11724) in
                               FStar_SMTEncoding_Util.mkApp uu____11720) in
                      let uu____11729 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___131_11731  ->
                                 match uu___131_11731 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11732 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11735 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11735))) in
                      if uu____11729
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11755;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11757;
                                FStar_Syntax_Syntax.lbeff = uu____11758;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11799 =
                                 let uu____11803 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11803 with
                                 | (tcenv',uu____11814,e_t) ->
                                     let uu____11818 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11825 -> failwith "Impossible" in
                                     (match uu____11818 with
                                      | (e1,t_norm1) ->
                                          ((let uu___166_11834 = env1 in
                                            {
                                              bindings =
                                                (uu___166_11834.bindings);
                                              depth = (uu___166_11834.depth);
                                              tcenv = tcenv';
                                              warn = (uu___166_11834.warn);
                                              cache = (uu___166_11834.cache);
                                              nolabels =
                                                (uu___166_11834.nolabels);
                                              use_zfuel_name =
                                                (uu___166_11834.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___166_11834.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___166_11834.current_module_name);
                                              activate_current_sigelt_facts =
                                                (uu___166_11834.activate_current_sigelt_facts)
                                            }), e1, t_norm1)) in
                               (match uu____11799 with
                                | (env',e1,t_norm1) ->
                                    let uu____11841 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11841 with
                                     | ((binders,body,uu____11853,uu____11854),curry)
                                         ->
                                         ((let uu____11861 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11861
                                           then
                                             let uu____11862 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11863 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11862 uu____11863
                                           else ());
                                          (let uu____11865 =
                                             encode_binders None binders env' in
                                           match uu____11865 with
                                           | (vars,guards,env'1,binder_decls,uu____11881)
                                               ->
                                               let body1 =
                                                 let uu____11889 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11889
                                                 then
                                                   reify_body env'1.tcenv
                                                     body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11892 =
                                                 let uu____11897 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11897
                                                 then
                                                   let uu____11903 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11904 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11903, uu____11904)
                                                 else
                                                   (let uu____11910 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11910)) in
                                               (match uu____11892 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11924 =
                                                        let uu____11928 =
                                                          let uu____11929 =
                                                            let uu____11935 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11935) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11929 in
                                                        let uu____11941 =
                                                          let uu____11943 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11943 in
                                                        (uu____11928,
                                                          uu____11941,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Term.Assume
                                                        uu____11924 in
                                                    let uu____11945 =
                                                      let uu____11947 =
                                                        let uu____11949 =
                                                          let uu____11951 =
                                                            let uu____11953 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11953 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11951 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11949 in
                                                      FStar_List.append
                                                        decls1 uu____11947 in
                                                    (uu____11945, env1))))))
                           | uu____11956 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11975 = varops.fresh "fuel" in
                             (uu____11975, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____11978 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12017  ->
                                     fun uu____12018  ->
                                       match (uu____12017, uu____12018) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12100 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12100 in
                                           let gtok =
                                             let uu____12102 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12102 in
                                           let env3 =
                                             let uu____12104 =
                                               let uu____12106 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12106 in
                                             push_free_var env2 flid gtok
                                               uu____12104 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____11978 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12192
                                 t_norm uu____12194 =
                                 match (uu____12192, uu____12194) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12221;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12222;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12239 =
                                       let uu____12243 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12243 with
                                       | (tcenv',uu____12258,e_t) ->
                                           let uu____12262 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12269 ->
                                                 failwith "Impossible" in
                                           (match uu____12262 with
                                            | (e1,t_norm1) ->
                                                ((let uu___167_12278 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___167_12278.bindings);
                                                    depth =
                                                      (uu___167_12278.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___167_12278.warn);
                                                    cache =
                                                      (uu___167_12278.cache);
                                                    nolabels =
                                                      (uu___167_12278.nolabels);
                                                    use_zfuel_name =
                                                      (uu___167_12278.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___167_12278.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___167_12278.current_module_name);
                                                    activate_current_sigelt_facts
                                                      =
                                                      (uu___167_12278.activate_current_sigelt_facts)
                                                  }), e1, t_norm1)) in
                                     (match uu____12239 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12288 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12288
                                            then
                                              let uu____12289 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12290 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12291 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12289 uu____12290
                                                uu____12291
                                            else ());
                                           (let uu____12293 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12293 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12315 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12315
                                                  then
                                                    let uu____12316 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12317 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12318 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12319 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12316 uu____12317
                                                      uu____12318 uu____12319
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12323 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12323 with
                                                  | (vars,guards,env'1,binder_decls,uu____12341)
                                                      ->
                                                      let decl_g =
                                                        let uu____12349 =
                                                          let uu____12355 =
                                                            let uu____12357 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12357 in
                                                          (g, uu____12355,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12349 in
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
                                                        let uu____12372 =
                                                          let uu____12376 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12376) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12372 in
                                                      let gsapp =
                                                        let uu____12382 =
                                                          let uu____12386 =
                                                            let uu____12388 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12388 ::
                                                              vars_tm in
                                                          (g, uu____12386) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12382 in
                                                      let gmax =
                                                        let uu____12392 =
                                                          let uu____12396 =
                                                            let uu____12398 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12398 ::
                                                              vars_tm in
                                                          (g, uu____12396) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12392 in
                                                      let body1 =
                                                        let uu____12402 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12402
                                                        then
                                                          reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12404 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12404 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12415
                                                               =
                                                               let uu____12419
                                                                 =
                                                                 let uu____12420
                                                                   =
                                                                   let uu____12428
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
                                                                    uu____12428) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12420 in
                                                               let uu____12439
                                                                 =
                                                                 let uu____12441
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12441 in
                                                               (uu____12419,
                                                                 uu____12439,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12415 in
                                                           let eqn_f =
                                                             let uu____12444
                                                               =
                                                               let uu____12448
                                                                 =
                                                                 let uu____12449
                                                                   =
                                                                   let uu____12455
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12455) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12449 in
                                                               (uu____12448,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12444 in
                                                           let eqn_g' =
                                                             let uu____12463
                                                               =
                                                               let uu____12467
                                                                 =
                                                                 let uu____12468
                                                                   =
                                                                   let uu____12474
                                                                    =
                                                                    let uu____12475
                                                                    =
                                                                    let uu____12478
                                                                    =
                                                                    let uu____12479
                                                                    =
                                                                    let uu____12483
                                                                    =
                                                                    let uu____12485
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12485
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12483) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12479 in
                                                                    (gsapp,
                                                                    uu____12478) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12475 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12474) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12468 in
                                                               (uu____12467,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12463 in
                                                           let uu____12497 =
                                                             let uu____12502
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12502
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12519)
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
                                                                    let uu____12534
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12534
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12537
                                                                    =
                                                                    let uu____12541
                                                                    =
                                                                    let uu____12542
                                                                    =
                                                                    let uu____12548
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12548) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12542 in
                                                                    (uu____12541,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Term.Assume
                                                                    uu____12537 in
                                                                 let uu____12559
                                                                   =
                                                                   let uu____12563
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12563
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12571
                                                                    =
                                                                    let uu____12573
                                                                    =
                                                                    let uu____12574
                                                                    =
                                                                    let uu____12578
                                                                    =
                                                                    let uu____12579
                                                                    =
                                                                    let uu____12585
                                                                    =
                                                                    let uu____12586
                                                                    =
                                                                    let uu____12589
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12589,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12586 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12585) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12579 in
                                                                    (uu____12578,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12574 in
                                                                    [uu____12573] in
                                                                    (d3,
                                                                    uu____12571) in
                                                                 (match uu____12559
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12497
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
                               let uu____12624 =
                                 let uu____12631 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12667  ->
                                      fun uu____12668  ->
                                        match (uu____12667, uu____12668) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12754 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12754 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12631 in
                               (match uu____12624 with
                                | (decls2,eqns,env01) ->
                                    let uu____12794 =
                                      let isDeclFun uu___132_12802 =
                                        match uu___132_12802 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12803 -> true
                                        | uu____12809 -> false in
                                      let uu____12810 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12810
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12794 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12837 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12837
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
        let uu____12870 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____12870 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____12873 = encode_sigelt' env se in
      match uu____12873 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12883 =
                  let uu____12884 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____12884 in
                [uu____12883]
            | uu____12885 ->
                let uu____12886 =
                  let uu____12888 =
                    let uu____12889 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12889 in
                  uu____12888 :: g in
                let uu____12890 =
                  let uu____12892 =
                    let uu____12893 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12893 in
                  [uu____12892] in
                FStar_List.append uu____12886 uu____12890 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12901 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12910 =
            let uu____12911 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12911 Prims.op_Negation in
          if uu____12910
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12931 ->
                   let uu____12932 =
                     let uu____12935 =
                       let uu____12936 =
                         let uu____12951 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12951) in
                       FStar_Syntax_Syntax.Tm_abs uu____12936 in
                     FStar_Syntax_Syntax.mk uu____12935 in
                   uu____12932 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13004 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13004 with
               | (aname,atok,env2) ->
                   let uu____13014 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13014 with
                    | (formals,uu____13024) ->
                        let uu____13031 =
                          let uu____13034 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13034 env2 in
                        (match uu____13031 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13042 =
                                 let uu____13043 =
                                   let uu____13049 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13057  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13049,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13043 in
                               [uu____13042;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13064 =
                               let aux uu____13093 uu____13094 =
                                 match (uu____13093, uu____13094) with
                                 | ((bv,uu____13121),(env3,acc_sorts,acc)) ->
                                     let uu____13142 = gen_term_var env3 bv in
                                     (match uu____13142 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13064 with
                              | (uu____13180,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13194 =
                                      let uu____13198 =
                                        let uu____13199 =
                                          let uu____13205 =
                                            let uu____13206 =
                                              let uu____13209 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13209) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13206 in
                                          ([[app]], xs_sorts, uu____13205) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13199 in
                                      (uu____13198, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Term.Assume uu____13194 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13221 =
                                      let uu____13225 =
                                        let uu____13226 =
                                          let uu____13232 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13232) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13226 in
                                      (uu____13225,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Term.Assume uu____13221 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13242 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13242 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13258,uu____13259)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13260 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13260 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13271,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13276 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___133_13278  ->
                      match uu___133_13278 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13281 -> false)) in
            Prims.op_Negation uu____13276 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13287 = encode_top_level_val env fv t quals in
             match uu____13287 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13299 =
                   let uu____13301 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13301 in
                 (uu____13299, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13306 = encode_formula f env in
          (match uu____13306 with
           | (f1,decls) ->
               let g =
                 let uu____13315 =
                   let uu____13316 =
                     let uu____13320 =
                       let uu____13322 =
                         let uu____13323 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13323 in
                       Some uu____13322 in
                     let uu____13324 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13320, uu____13324) in
                   FStar_SMTEncoding_Term.Assume uu____13316 in
                 [uu____13315] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13328,uu____13329) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13335 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13342 =
                       let uu____13347 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13347.FStar_Syntax_Syntax.fv_name in
                     uu____13342.FStar_Syntax_Syntax.v in
                   let uu____13351 =
                     let uu____13352 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13352 in
                   if uu____13351
                   then
                     let val_decl =
                       let uu___168_13367 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___168_13367.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___168_13367.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___168_13367.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13371 = encode_sigelt' env1 val_decl in
                     match uu____13371 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13335 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13388,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13390;
                          FStar_Syntax_Syntax.lbtyp = uu____13391;
                          FStar_Syntax_Syntax.lbeff = uu____13392;
                          FStar_Syntax_Syntax.lbdef = uu____13393;_}::[]),uu____13394,uu____13395)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13409 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13409 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13432 =
                   let uu____13434 =
                     let uu____13435 =
                       let uu____13439 =
                         let uu____13440 =
                           let uu____13446 =
                             let uu____13447 =
                               let uu____13450 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13450) in
                             FStar_SMTEncoding_Util.mkEq uu____13447 in
                           ([[b2t_x]], [xx], uu____13446) in
                         FStar_SMTEncoding_Util.mkForall uu____13440 in
                       (uu____13439, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Term.Assume uu____13435 in
                   [uu____13434] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13432 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13467,uu____13468,uu____13469)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___134_13475  ->
                  match uu___134_13475 with
                  | FStar_Syntax_Syntax.Discriminator uu____13476 -> true
                  | uu____13477 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13479,lids,uu____13481) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13488 =
                     let uu____13489 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13489.FStar_Ident.idText in
                   uu____13488 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___135_13491  ->
                     match uu___135_13491 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13492 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13495,uu____13496)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___136_13506  ->
                  match uu___136_13506 with
                  | FStar_Syntax_Syntax.Projector uu____13507 -> true
                  | uu____13510 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13517 = try_lookup_free_var env l in
          (match uu____13517 with
           | Some uu____13521 -> ([], env)
           | None  ->
               let se1 =
                 let uu___169_13524 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___169_13524.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___169_13524.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13530,uu____13531) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13543) ->
          let uu____13548 = encode_sigelts env ses in
          (match uu____13548 with
           | (g,env1) ->
               let uu____13558 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___137_13568  ->
                         match uu___137_13568 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13569,Some "inversion axiom",uu____13570)
                             -> false
                         | uu____13572 -> true)) in
               (match uu____13558 with
                | (g',inversions) ->
                    let uu____13581 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___138_13591  ->
                              match uu___138_13591 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13592 ->
                                  true
                              | uu____13598 -> false)) in
                    (match uu____13581 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13609,tps,k,uu____13612,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___139_13622  ->
                    match uu___139_13622 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13623 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13630 = c in
              match uu____13630 with
              | (name,args,uu____13634,uu____13635,uu____13636) ->
                  let uu____13639 =
                    let uu____13640 =
                      let uu____13646 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13653  ->
                                match uu____13653 with
                                | (uu____13657,sort,uu____13659) -> sort)) in
                      (name, uu____13646, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13640 in
                  [uu____13639]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13677 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13680 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13680 FStar_Option.isNone)) in
            if uu____13677
            then []
            else
              (let uu____13697 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13697 with
               | (xxsym,xx) ->
                   let uu____13703 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13714  ->
                             fun l  ->
                               match uu____13714 with
                               | (out,decls) ->
                                   let uu____13726 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13726 with
                                    | (uu____13732,data_t) ->
                                        let uu____13734 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13734 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13763 =
                                                 let uu____13764 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13764.FStar_Syntax_Syntax.n in
                                               match uu____13763 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13772,indices) ->
                                                   indices
                                               | uu____13788 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13800  ->
                                                         match uu____13800
                                                         with
                                                         | (x,uu____13804) ->
                                                             let uu____13805
                                                               =
                                                               let uu____13806
                                                                 =
                                                                 let uu____13810
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13810,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13806 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13805)
                                                    env) in
                                             let uu____13812 =
                                               encode_args indices env1 in
                                             (match uu____13812 with
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
                                                      let uu____13832 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13840
                                                                 =
                                                                 let uu____13843
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13843,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13840)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13832
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13845 =
                                                      let uu____13846 =
                                                        let uu____13849 =
                                                          let uu____13850 =
                                                            let uu____13853 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13853,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13850 in
                                                        (out, uu____13849) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13846 in
                                                    (uu____13845,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13703 with
                    | (data_ax,decls) ->
                        let uu____13861 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13861 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13872 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13872 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13875 =
                                 let uu____13879 =
                                   let uu____13880 =
                                     let uu____13886 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13894 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13886,
                                       uu____13894) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13880 in
                                 let uu____13902 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13879, (Some "inversion axiom"),
                                   uu____13902) in
                               FStar_SMTEncoding_Term.Assume uu____13875 in
                             let pattern_guarded_inversion =
                               let uu____13906 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13906
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13914 =
                                   let uu____13915 =
                                     let uu____13919 =
                                       let uu____13920 =
                                         let uu____13926 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13934 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13926, uu____13934) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13920 in
                                     let uu____13942 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13919, (Some "inversion axiom"),
                                       uu____13942) in
                                   FStar_SMTEncoding_Term.Assume uu____13915 in
                                 [uu____13914]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13945 =
            let uu____13953 =
              let uu____13954 = FStar_Syntax_Subst.compress k in
              uu____13954.FStar_Syntax_Syntax.n in
            match uu____13953 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13983 -> (tps, k) in
          (match uu____13945 with
           | (formals,res) ->
               let uu____13998 = FStar_Syntax_Subst.open_term formals res in
               (match uu____13998 with
                | (formals1,res1) ->
                    let uu____14005 = encode_binders None formals1 env in
                    (match uu____14005 with
                     | (vars,guards,env',binder_decls,uu____14020) ->
                         let uu____14027 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14027 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14040 =
                                  let uu____14044 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14044) in
                                FStar_SMTEncoding_Util.mkApp uu____14040 in
                              let uu____14049 =
                                let tname_decl =
                                  let uu____14055 =
                                    let uu____14056 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14071  ->
                                              match uu____14071 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14079 = varops.next_id () in
                                    (tname, uu____14056,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14079, false) in
                                  constructor_or_logic_type_decl uu____14055 in
                                let uu____14084 =
                                  match vars with
                                  | [] ->
                                      let uu____14091 =
                                        let uu____14092 =
                                          let uu____14094 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14094 in
                                        push_free_var env1 t tname
                                          uu____14092 in
                                      ([], uu____14091)
                                  | uu____14098 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14104 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14104 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14113 =
                                          let uu____14117 =
                                            let uu____14118 =
                                              let uu____14126 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14126) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14118 in
                                          (uu____14117,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____14113 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14084 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14049 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14149 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14149 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14163 =
                                               let uu____14164 =
                                                 let uu____14168 =
                                                   let uu____14169 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14169 in
                                                 (uu____14168,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14164 in
                                             [uu____14163]
                                           else [] in
                                         let uu____14172 =
                                           let uu____14174 =
                                             let uu____14176 =
                                               let uu____14177 =
                                                 let uu____14181 =
                                                   let uu____14182 =
                                                     let uu____14188 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14188) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14182 in
                                                 (uu____14181, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14177 in
                                             [uu____14176] in
                                           FStar_List.append karr uu____14174 in
                                         FStar_List.append decls1 uu____14172 in
                                   let aux =
                                     let uu____14197 =
                                       let uu____14199 =
                                         inversion_axioms tapp vars in
                                       let uu____14201 =
                                         let uu____14203 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14203] in
                                       FStar_List.append uu____14199
                                         uu____14201 in
                                     FStar_List.append kindingAx uu____14197 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14208,uu____14209,uu____14210,uu____14211,uu____14212)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14217,t,uu____14219,n_tps,uu____14221) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14226 = new_term_constant_and_tok_from_lid env d in
          (match uu____14226 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14237 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14237 with
                | (formals,t_res) ->
                    let uu____14259 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14259 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14268 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14268 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14306 =
                                            mk_term_projector_name d x in
                                          (uu____14306,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14308 =
                                  let uu____14318 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14318, true) in
                                FStar_All.pipe_right uu____14308
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
                              let uu____14340 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14340 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14348::uu____14349 ->
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
                                         let uu____14374 =
                                           let uu____14380 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14380) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14374
                                     | uu____14393 -> tok_typing in
                                   let uu____14398 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14398 with
                                    | (vars',guards',env'',decls_formals,uu____14413)
                                        ->
                                        let uu____14420 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14420 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14439 ->
                                                   let uu____14443 =
                                                     let uu____14444 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14444 in
                                                   [uu____14443] in
                                             let encode_elim uu____14451 =
                                               let uu____14452 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14452 with
                                               | (head1,args) ->
                                                   let uu____14481 =
                                                     let uu____14482 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14482.FStar_Syntax_Syntax.n in
                                                   (match uu____14481 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                      ({
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           FStar_Syntax_Syntax.Tm_fvar
                                                           fv;
                                                         FStar_Syntax_Syntax.tk
                                                           = _;
                                                         FStar_Syntax_Syntax.pos
                                                           = _;
                                                         FStar_Syntax_Syntax.vars
                                                           = _;_},_)
                                                      |FStar_Syntax_Syntax.Tm_fvar
                                                      fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14500 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14500
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
                                                                 | uu____14526
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14534
                                                                    =
                                                                    let uu____14535
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14535 in
                                                                    if
                                                                    uu____14534
                                                                    then
                                                                    let uu____14542
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14542]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14544
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14557
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14557
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14579
                                                                    =
                                                                    let uu____14583
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14583 in
                                                                    (match uu____14579
                                                                    with
                                                                    | 
                                                                    (uu____14590,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14596
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14596
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14598
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14598
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
                                                             (match uu____14544
                                                              with
                                                              | (uu____14606,arg_vars,elim_eqns_or_guards,uu____14609)
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
                                                                    let uu____14628
                                                                    =
                                                                    let uu____14632
                                                                    =
                                                                    let uu____14633
                                                                    =
                                                                    let uu____14639
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14645
                                                                    =
                                                                    let uu____14646
                                                                    =
                                                                    let uu____14649
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14649) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14646 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14639,
                                                                    uu____14645) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14633 in
                                                                    (uu____14632,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14628 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14662
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14662,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14664
                                                                    =
                                                                    let uu____14668
                                                                    =
                                                                    let uu____14669
                                                                    =
                                                                    let uu____14675
                                                                    =
                                                                    let uu____14678
                                                                    =
                                                                    let uu____14680
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14680] in
                                                                    [uu____14678] in
                                                                    let uu____14683
                                                                    =
                                                                    let uu____14684
                                                                    =
                                                                    let uu____14687
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14688
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14687,
                                                                    uu____14688) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14684 in
                                                                    (uu____14675,
                                                                    [x],
                                                                    uu____14683) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14669 in
                                                                    let uu____14698
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14668,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14698) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14664
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14703
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
                                                                    (let uu____14718
                                                                    =
                                                                    let uu____14719
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14719
                                                                    dapp1 in
                                                                    [uu____14718]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14703
                                                                    FStar_List.flatten in
                                                                    let uu____14723
                                                                    =
                                                                    let uu____14727
                                                                    =
                                                                    let uu____14728
                                                                    =
                                                                    let uu____14734
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14740
                                                                    =
                                                                    let uu____14741
                                                                    =
                                                                    let uu____14744
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14744) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14741 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14734,
                                                                    uu____14740) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14728 in
                                                                    (uu____14727,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14723) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14754 ->
                                                        ((let uu____14756 =
                                                            let uu____14757 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14758 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14757
                                                              uu____14758 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14756);
                                                         ([], []))) in
                                             let uu____14761 = encode_elim () in
                                             (match uu____14761 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14773 =
                                                      let uu____14775 =
                                                        let uu____14777 =
                                                          let uu____14779 =
                                                            let uu____14781 =
                                                              let uu____14782
                                                                =
                                                                let uu____14788
                                                                  =
                                                                  let uu____14790
                                                                    =
                                                                    let uu____14791
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14791 in
                                                                  Some
                                                                    uu____14790 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14788) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14782 in
                                                            [uu____14781] in
                                                          let uu____14794 =
                                                            let uu____14796 =
                                                              let uu____14798
                                                                =
                                                                let uu____14800
                                                                  =
                                                                  let uu____14802
                                                                    =
                                                                    let uu____14804
                                                                    =
                                                                    let uu____14806
                                                                    =
                                                                    let uu____14807
                                                                    =
                                                                    let uu____14811
                                                                    =
                                                                    let uu____14812
                                                                    =
                                                                    let uu____14818
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14818) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14812 in
                                                                    (uu____14811,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14807 in
                                                                    let uu____14825
                                                                    =
                                                                    let uu____14827
                                                                    =
                                                                    let uu____14828
                                                                    =
                                                                    let uu____14832
                                                                    =
                                                                    let uu____14833
                                                                    =
                                                                    let uu____14839
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14845
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14839,
                                                                    uu____14845) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14833 in
                                                                    (uu____14832,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14828 in
                                                                    [uu____14827] in
                                                                    uu____14806
                                                                    ::
                                                                    uu____14825 in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14804 in
                                                                  FStar_List.append
                                                                    uu____14802
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14800 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14798 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14796 in
                                                          FStar_List.append
                                                            uu____14779
                                                            uu____14794 in
                                                        FStar_List.append
                                                          decls3 uu____14777 in
                                                      FStar_List.append
                                                        decls2 uu____14775 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14773 in
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
           (fun uu____14866  ->
              fun se  ->
                match uu____14866 with
                | (g,env1) ->
                    let uu____14878 = encode_sigelt env1 se in
                    (match uu____14878 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14914 =
        match uu____14914 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14932 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14937 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14937
                   then
                     let uu____14938 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14939 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14940 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14938 uu____14939 uu____14940
                   else ());
                  (let uu____14942 = encode_term t1 env1 in
                   match uu____14942 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14952 =
                         let uu____14956 =
                           let uu____14957 =
                             let uu____14958 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____14958
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____14957 in
                         new_term_constant_from_string env1 x uu____14956 in
                       (match uu____14952 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____14969 = FStar_Options.log_queries () in
                              if uu____14969
                              then
                                let uu____14971 =
                                  let uu____14972 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____14973 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____14974 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14972 uu____14973 uu____14974 in
                                Some uu____14971
                              else None in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym in
                              FStar_SMTEncoding_Term.Assume
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14985,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____14994 = encode_free_var env1 fv t t_norm [] in
                 (match uu____14994 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____15013 = encode_sigelt env1 se in
                 (match uu____15013 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15023 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15023 with | (uu____15035,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15080  ->
            match uu____15080 with
            | (l,uu____15087,uu____15088) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15109  ->
            match uu____15109 with
            | (l,uu____15117,uu____15118) ->
                let uu____15123 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____15124 =
                  let uu____15126 =
                    let uu____15127 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15127 in
                  [uu____15126] in
                uu____15123 :: uu____15124)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15138 =
      let uu____15140 =
        let uu____15141 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15143 =
          let uu____15144 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15144 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15141;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15143;
          activate_current_sigelt_facts = []
        } in
      [uu____15140] in
    FStar_ST.write last_env uu____15138
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15154 = FStar_ST.read last_env in
      match uu____15154 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15160 ->
          let uu___170_15162 = e in
          let uu____15163 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___170_15162.bindings);
            depth = (uu___170_15162.depth);
            tcenv;
            warn = (uu___170_15162.warn);
            cache = (uu___170_15162.cache);
            nolabels = (uu___170_15162.nolabels);
            use_zfuel_name = (uu___170_15162.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___170_15162.encode_non_total_function_typ);
            current_module_name = uu____15163;
            activate_current_sigelt_facts =
              (uu___170_15162.activate_current_sigelt_facts)
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15167 = FStar_ST.read last_env in
    match uu____15167 with
    | [] -> failwith "Empty env stack"
    | uu____15172::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15180  ->
    let uu____15181 = FStar_ST.read last_env in
    match uu____15181 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___171_15192 = hd1 in
          {
            bindings = (uu___171_15192.bindings);
            depth = (uu___171_15192.depth);
            tcenv = (uu___171_15192.tcenv);
            warn = (uu___171_15192.warn);
            cache = refs;
            nolabels = (uu___171_15192.nolabels);
            use_zfuel_name = (uu___171_15192.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___171_15192.encode_non_total_function_typ);
            current_module_name = (uu___171_15192.current_module_name);
            activate_current_sigelt_facts =
              (uu___171_15192.activate_current_sigelt_facts)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15198  ->
    let uu____15199 = FStar_ST.read last_env in
    match uu____15199 with
    | [] -> failwith "Popping an empty stack"
    | uu____15204::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15212  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15215  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15218  ->
    let uu____15219 = FStar_ST.read last_env in
    match uu____15219 with
    | hd1::uu____15225::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15231 -> failwith "Impossible"
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
type fact_db_id =
  | Name of FStar_Ident.lid
  | Namespace of FStar_Ident.lid
  | Tag of Prims.string
  | Global
let uu___is_Name: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____15276 -> false
let __proj__Name__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_Namespace: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____15288 -> false
let __proj__Namespace__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Namespace _0 -> _0
let uu___is_Tag: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____15300 -> false
let __proj__Tag__item___0: fact_db_id -> Prims.string =
  fun projectee  -> match projectee with | Tag _0 -> _0
let uu___is_Global: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Global  -> true | uu____15311 -> false
let term_of_string: Prims.string -> FStar_SMTEncoding_Term.term =
  fun s  ->
    let r = FStar_Range.dummyRange in
    encode_const
      (FStar_Const.Const_string ((FStar_Util.unicode_of_string s), r))
let string_of_fact_db_id: fact_db_id -> Prims.string =
  fun uu___140_15319  ->
    match uu___140_15319 with
    | Name l -> Prims.strcat "Name@" l.FStar_Ident.str
    | Namespace l -> Prims.strcat "Namespace@" l.FStar_Ident.str
    | Tag s -> Prims.strcat "Tag@" s
    | Global  -> "__GLOBAL__"
let encode_fact_db_id:
  env_t ->
    fact_db_id ->
      (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun env  ->
    fun f  ->
      let f_str = string_of_fact_db_id f in
      let raw_term = term_of_string f_str in
      let uu____15335 =
        let uu____15337 = FStar_SMTEncoding_Term.print_smt_term raw_term in
        FStar_Util.smap_try_find env.cache uu____15337 in
      match uu____15335 with
      | Some cache_entry ->
          let uu____15341 =
            FStar_SMTEncoding_Term.mkFreeV
              ((cache_entry.cache_symbol_name),
                FStar_SMTEncoding_Term.Term_sort) FStar_Range.dummyRange in
          (uu____15341, [])
      | None  ->
          let fact_db_name = varops.mk_unique f_str in
          let decl =
            FStar_SMTEncoding_Term.DefineFun
              (fact_db_name, [], FStar_SMTEncoding_Term.Term_sort, raw_term,
                None) in
          ((let uu____15348 = FStar_SMTEncoding_Term.print_smt_term raw_term in
            FStar_Util.smap_add env.cache uu____15348
              (mk_cache_entry env fact_db_name [] [decl]));
           (let uu____15349 =
              FStar_SMTEncoding_Term.mkFreeV
                (fact_db_name, FStar_SMTEncoding_Term.Term_sort)
                FStar_Range.dummyRange in
            (uu____15349, [decl])))
type fact_db_ids = fact_db_id Prims.list
let open_fact_db_tags: env_t -> fact_db_id Prims.list = fun env  -> []
let place_decl_in_fact_dbs:
  env_t ->
    FStar_SMTEncoding_Term.term Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun fact_dbs  ->
      fun d  ->
        match (fact_dbs, d) with
        | (uu____15367::uu____15368,FStar_SMTEncoding_Term.Assume
           (term,caption,assumption_name)) ->
            let tag = ("guard", FStar_SMTEncoding_Term.Bool_sort) in
            let tag_tm = FStar_SMTEncoding_Util.mkFreeV tag in
            let fact_db_triggers =
              FStar_All.pipe_right fact_dbs
                (FStar_List.map
                   (fun fact_db  ->
                      let uu____15386 =
                        FStar_SMTEncoding_Term.mk_ActiveFactDB fact_db tag_tm in
                      [uu____15386])) in
            let guarded_term_body =
              FStar_SMTEncoding_Term.mkImp (tag_tm, term)
                term.FStar_SMTEncoding_Term.rng in
            let guarded_term =
              FStar_SMTEncoding_Term.mkForall
                (fact_db_triggers, [tag], guarded_term_body)
                guarded_term_body.FStar_SMTEncoding_Term.rng in
            FStar_SMTEncoding_Term.Assume
              (guarded_term, caption, assumption_name)
        | uu____15398 -> d
let fact_dbs_for_lid: env_t -> FStar_Ident.lid -> fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15409 =
        let uu____15411 =
          let uu____15412 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          Namespace uu____15412 in
        let uu____15413 =
          let uu____15415 = open_fact_db_tags env in Global :: uu____15415 in
        uu____15411 :: uu____15413 in
      (Name lid) :: uu____15409
let activate_fact_db: env_t -> fact_db_id -> FStar_SMTEncoding_Term.decls_t =
  fun env  ->
    fun f  ->
      let uu____15423 = encode_fact_db_id env f in
      match uu____15423 with
      | (tm,decls) ->
          let trigger =
            let uu____15429 =
              FStar_SMTEncoding_Term.mkTrue FStar_Range.dummyRange in
            FStar_SMTEncoding_Term.mk_ActiveFactDB tm uu____15429 in
          let nm =
            FStar_Util.format1 "@activating_fact_db_%s"
              (string_of_fact_db_id f) in
          (FStar_SMTEncoding_Term.Assume (trigger, (Some nm), nm)) :: decls
let encode_top_level_facts:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun se  ->
      let uu____15441 =
        let uu____15447 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____15447 with
        | None  -> ([], [], env)
        | Some l ->
            let uu____15457 =
              let uu____15462 =
                let uu____15466 = fact_dbs_for_lid env l in
                FStar_All.pipe_right uu____15466
                  (FStar_List.map (encode_fact_db_id env)) in
              FStar_All.pipe_right uu____15462 FStar_List.unzip in
            (match uu____15457 with
             | (fact_db_terms,fact_db_decls) ->
                 let env1 =
                   let uu___172_15493 = env in
                   let uu____15494 = activate_fact_db env (Name l) in
                   {
                     bindings = (uu___172_15493.bindings);
                     depth = (uu___172_15493.depth);
                     tcenv = (uu___172_15493.tcenv);
                     warn = (uu___172_15493.warn);
                     cache = (uu___172_15493.cache);
                     nolabels = (uu___172_15493.nolabels);
                     use_zfuel_name = (uu___172_15493.use_zfuel_name);
                     encode_non_total_function_typ =
                       (uu___172_15493.encode_non_total_function_typ);
                     current_module_name =
                       (uu___172_15493.current_module_name);
                     activate_current_sigelt_facts = uu____15494
                   } in
                 (fact_db_terms, (FStar_List.flatten fact_db_decls), env1)) in
      match uu____15441 with
      | (fact_db_terms,fact_db_decls,env1) ->
          let uu____15508 = encode_sigelt env1 se in
          (match uu____15508 with
           | (g,env2) ->
               let g1 =
                 FStar_All.pipe_right g
                   (FStar_List.map
                      (place_decl_in_fact_dbs env2 fact_db_terms)) in
               let g2 = FStar_List.append fact_db_decls g1 in
               let env3 =
                 let uu___173_15522 = env2 in
                 {
                   bindings = (uu___173_15522.bindings);
                   depth = (uu___173_15522.depth);
                   tcenv = (uu___173_15522.tcenv);
                   warn = (uu___173_15522.warn);
                   cache = (uu___173_15522.cache);
                   nolabels = (uu___173_15522.nolabels);
                   use_zfuel_name = (uu___173_15522.use_zfuel_name);
                   encode_non_total_function_typ =
                     (uu___173_15522.encode_non_total_function_typ);
                   current_module_name = (uu___173_15522.current_module_name);
                   activate_current_sigelt_facts = []
                 } in
               (g2, env3))
let encode_sig:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____15537 = FStar_Options.log_queries () in
        if uu____15537
        then
          let uu____15539 =
            let uu____15540 =
              let uu____15541 =
                let uu____15542 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15542 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15541 in
            FStar_SMTEncoding_Term.Caption uu____15540 in
          uu____15539 :: decls
        else decls in
      let env =
        let uu____15549 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15549 tcenv in
      let uu____15550 = encode_top_level_facts env se in
      match uu____15550 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15559 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15559))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15570 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15570
       then
         let uu____15571 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15571
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15592  ->
                 fun se  ->
                   match uu____15592 with
                   | (g,env2) ->
                       let uu____15604 = encode_top_level_facts env2 se in
                       (match uu____15604 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15617 =
         encode_signature
           (let uu___174_15621 = env in
            {
              bindings = (uu___174_15621.bindings);
              depth = (uu___174_15621.depth);
              tcenv = (uu___174_15621.tcenv);
              warn = false;
              cache = (uu___174_15621.cache);
              nolabels = (uu___174_15621.nolabels);
              use_zfuel_name = (uu___174_15621.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___174_15621.encode_non_total_function_typ);
              current_module_name = (uu___174_15621.current_module_name);
              activate_current_sigelt_facts =
                (uu___174_15621.activate_current_sigelt_facts)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15617 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15633 = FStar_Options.log_queries () in
             if uu____15633
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___175_15638 = env1 in
               {
                 bindings = (uu___175_15638.bindings);
                 depth = (uu___175_15638.depth);
                 tcenv = (uu___175_15638.tcenv);
                 warn = true;
                 cache = (uu___175_15638.cache);
                 nolabels = (uu___175_15638.nolabels);
                 use_zfuel_name = (uu___175_15638.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___175_15638.encode_non_total_function_typ);
                 current_module_name = (uu___175_15638.current_module_name);
                 activate_current_sigelt_facts =
                   (uu___175_15638.activate_current_sigelt_facts)
               });
            (let uu____15640 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15640
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls1)))
let encode_query:
  (Prims.unit -> Prims.string) Prims.option ->
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
        (let uu____15675 =
           let uu____15676 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15676.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15675);
        (let env =
           let uu____15678 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15678 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15685 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15706 = aux rest in
                 (match uu____15706 with
                  | (out,rest1) ->
                      let t =
                        let uu____15724 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15724 with
                        | Some uu____15728 ->
                            let uu____15729 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15729
                              x.FStar_Syntax_Syntax.sort
                        | uu____15730 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15733 =
                        let uu____15735 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___176_15736 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___176_15736.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___176_15736.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15735 :: out in
                      (uu____15733, rest1))
             | uu____15739 -> ([], bindings1) in
           let uu____15743 = aux bindings in
           match uu____15743 with
           | (closing,bindings1) ->
               let uu____15757 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15757, bindings1) in
         match uu____15685 with
         | (q1,bindings1) ->
             let uu____15770 =
               let uu____15773 =
                 FStar_List.filter
                   (fun uu___141_15775  ->
                      match uu___141_15775 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15776 ->
                          false
                      | uu____15780 -> true) bindings1 in
               encode_env_bindings env uu____15773 in
             (match uu____15770 with
              | (env_decls,env1) ->
                  ((let uu____15791 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15791
                    then
                      let uu____15792 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15792
                    else ());
                   (let uu____15794 = encode_formula q1 env1 in
                    match uu____15794 with
                    | (phi,qdecls) ->
                        let uu____15806 =
                          let uu____15809 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15809 phi in
                        (match uu____15806 with
                         | (labels,phi1) ->
                             let uu____15819 = encode_labels labels in
                             (match uu____15819 with
                              | (label_prefix,label_suffix) ->
                                  let fact_db_decls =
                                    activate_fact_db env1 Global in
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append fact_db_decls
                                         (FStar_List.append label_prefix
                                            qdecls)) in
                                  let qry =
                                    let uu____15841 =
                                      let uu____15845 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15846 =
                                        varops.mk_unique "@query" in
                                      (uu____15845, (Some "query"),
                                        uu____15846) in
                                    FStar_SMTEncoding_Term.Assume uu____15841 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15859 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15859 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15861 = encode_formula q env in
       match uu____15861 with
       | (f,uu____15865) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15867) -> true
             | uu____15870 -> false)))