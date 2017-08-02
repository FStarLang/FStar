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
  | FStar_Pervasives_Native.Some (FStar_Util.Inl l1) ->
      let uu____114 =
        let uu____117 =
          let uu____118 =
            let uu____121 = l1.FStar_Syntax_Syntax.comp () in
            FStar_Syntax_Subst.subst_comp s uu____121 in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____118 in
        FStar_Util.Inl uu____117 in
      FStar_Pervasives_Native.Some uu____114
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
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
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
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____509 ->
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
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____521 in
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
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id = next_id1 () in
        let f =
          let uu____616 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____616 in
        let top_scope =
          let uu____619 =
            let uu____624 = FStar_ST.read scopes in FStar_List.hd uu____624 in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____619 in
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
  | Binding_var of (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
  FStar_Pervasives_Native.tuple2
  | Binding_fvar of
  (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                     FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple4
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____827 -> false
let __proj__Binding_var__item___0:
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____851 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar v1 = (v1, FStar_Pervasives_Native.None)
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
let caption_t:
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____1093 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1093
      then
        let uu____1095 = FStar_Syntax_Print.term_to_string t in
        FStar_Pervasives_Native.Some uu____1095
      else FStar_Pervasives_Native.None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1106 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1106)
let gen_term_var:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
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
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
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
      Prims.string ->
        (Prims.string,FStar_SMTEncoding_Term.term,env_t)
          FStar_Pervasives_Native.tuple3
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
                 FStar_Pervasives_Native.Some (b, t)
             | uu____1181 -> FStar_Pervasives_Native.None) in
      let uu____1184 = aux a in
      match uu____1184 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a in
          let uu____1191 = aux a2 in
          (match uu____1191 with
           | FStar_Pervasives_Native.None  ->
               let uu____1197 =
                 let uu____1198 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1199 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1198 uu____1199 in
               failwith uu____1197
           | FStar_Pervasives_Native.Some (b,t) -> t)
      | FStar_Pervasives_Native.Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,Prims.string,env_t) FStar_Pervasives_Native.tuple3
  =
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
                FStar_All.pipe_left
                  (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                  uu____1233 in
              (x, fname, uu____1231, FStar_Pervasives_Native.None) in
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
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___105_1255  ->
           match uu___105_1255 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____1277 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1289 =
        lookup_binding env
          (fun uu___106_1291  ->
             match uu___106_1291 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____1301 -> FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____1289 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun a  ->
      let uu____1314 = try_lookup_lid env a in
      match uu____1314 with
      | FStar_Pervasives_Native.None  ->
          let uu____1331 =
            let uu____1332 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1332 in
          failwith uu____1331
      | FStar_Pervasives_Native.Some s -> s
let push_free_var:
  env_t ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___133_1363 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
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
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
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
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____1408 = try_lookup_lid env l in
      match uu____1408 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____1435 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1440,fuel::[]) ->
                         let uu____1443 =
                           let uu____1444 =
                             let uu____1445 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1445
                               FStar_Pervasives_Native.fst in
                           FStar_Util.starts_with uu____1444 "fuel" in
                         if uu____1443
                         then
                           let uu____1447 =
                             let uu____1448 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1448
                               fuel in
                           FStar_All.pipe_left
                             (fun _0_30  ->
                                FStar_Pervasives_Native.Some _0_30)
                             uu____1447
                         else FStar_Pervasives_Native.Some t
                     | uu____1451 -> FStar_Pervasives_Native.Some t)
                | uu____1452 -> FStar_Pervasives_Native.None))
let lookup_free_var env a =
  let uu____1470 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1470 with
  | FStar_Pervasives_Native.Some t -> t
  | FStar_Pervasives_Native.None  ->
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
       | FStar_Pervasives_Native.Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1544;
             FStar_SMTEncoding_Term.rng = uu____1545;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1553 ->
           (match sym with
            | FStar_Pervasives_Native.None  ->
                ((FStar_SMTEncoding_Term.Var name), [])
            | FStar_Pervasives_Native.Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1567 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___107_1576  ->
           match uu___107_1576 with
           | Binding_fvar (uu____1578,nm',tok,uu____1581) when nm = nm' ->
               tok
           | uu____1586 -> FStar_Pervasives_Native.None)
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
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
    FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
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
          (uu____1785,uu____1786,FStar_Pervasives_Native.Some (FStar_Util.Inr
           (l,flags)))
          ->
          ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___108_1815  ->
                  match uu___108_1815 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1816 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1817,uu____1818,FStar_Pervasives_Native.Some (FStar_Util.Inl
           lc))
          -> FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
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
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____1876 uu____1878 FStar_Pervasives_Native.None
let mk_Apply:
  FStar_SMTEncoding_Term.term ->
    (Prims.string,FStar_SMTEncoding_Term.sort) FStar_Pervasives_Native.tuple2
      Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match FStar_Pervasives_Native.snd var with
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
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
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
              if uu____1969
              then tok_of_name env f
              else FStar_Pervasives_Native.None
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
              if uu____1985
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____1990 -> FStar_Pervasives_Native.None in
        check_partial_applications body (FStar_List.rev vars)
type label =
  (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
    FStar_Pervasives_Native.tuple3
type labels = label Prims.list
type pattern =
  {
  pat_vars:
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list;}
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
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
        let uu____2101 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2101
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.Some uu____2103) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (s,uu____2112) -> varops.string_const s
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2115 =
          let uu____2116 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2116 in
        failwith uu____2115
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2135 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2143 ->
            let uu____2148 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2148
        | uu____2149 ->
            if norm1
            then let uu____2150 = whnf env t1 in aux false uu____2150
            else
              (let uu____2152 =
                 let uu____2153 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2154 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2153 uu____2154 in
               failwith uu____2152) in
      aux true t0
let curried_arrow_formals_comp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | uu____2175 ->
        let uu____2176 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2176)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2204::uu____2205::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Parser_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2208::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
  | uu____2210 -> false
let rec encode_binders:
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list,FStar_SMTEncoding_Term.term
                                                Prims.list,env_t,FStar_SMTEncoding_Term.decls_t,
          FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple5
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____2348 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2348
         then
           let uu____2349 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2349
         else ());
        (let uu____2351 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2387  ->
                   fun b  ->
                     match uu____2387 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2430 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____2439 = gen_term_var env1 x in
                           match uu____2439 with
                           | (xxsym,xx,env') ->
                               let uu____2453 =
                                 let uu____2456 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2456 env1 xx in
                               (match uu____2453 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2430 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2351 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))
and encode_term_pred:
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2544 = encode_term t env in
          match uu____2544 with
          | (t1,decls) ->
              let uu____2551 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2551, decls)
and encode_term_pred':
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2559 = encode_term t env in
          match uu____2559 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2568 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2568, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2570 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2570, decls))
and encode_arith_term:
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2576 = encode_args args_e env in
        match uu____2576 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2588 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____2595 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____2595 in
            let binary arg_tms1 =
              let uu____2604 =
                let uu____2605 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____2605 in
              let uu____2606 =
                let uu____2607 =
                  let uu____2608 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2608 in
                FStar_SMTEncoding_Term.unboxInt uu____2607 in
              (uu____2604, uu____2606) in
            let mk_default uu____2613 =
              let uu____2614 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2614 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____2659 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2659
              then
                let uu____2660 = let uu____2661 = mk_args ts in op uu____2661 in
                FStar_All.pipe_right uu____2660 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____2684 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____2684
              then
                let uu____2685 = binary ts in
                match uu____2685 with
                | (t1,t2) ->
                    let uu____2690 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____2690
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2693 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____2693
                 then
                   let uu____2694 = op (binary ts) in
                   FStar_All.pipe_right uu____2694
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ()) in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary in
            let minus = mk_l FStar_SMTEncoding_Util.mkMinus unary in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod in
            let ops =
              [(FStar_Parser_Const.op_Addition, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus)] in
            let uu____2784 =
              let uu____2790 =
                FStar_List.tryFind
                  (fun uu____2802  ->
                     match uu____2802 with
                     | (l,uu____2809) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____2790 FStar_Util.must in
            (match uu____2784 with
             | (uu____2834,op) ->
                 let uu____2842 = op arg_tms in (uu____2842, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2849 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2849
       then
         let uu____2850 = FStar_Syntax_Print.tag_of_term t in
         let uu____2851 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2852 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2850 uu____2851
           uu____2852
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2856 ->
           let uu____2877 =
             let uu____2878 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2879 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2880 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2881 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2878
               uu____2879 uu____2880 uu____2881 in
           failwith uu____2877
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2884 =
             let uu____2885 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2886 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2887 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2888 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2885
               uu____2886 uu____2887 uu____2888 in
           failwith uu____2884
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2892 =
             let uu____2893 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2893 in
           failwith uu____2892
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2898) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2928) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2937 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2937, [])
       | FStar_Syntax_Syntax.Tm_type uu____2943 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2946) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2952 = encode_const c in (uu____2952, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2967 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2967 with
            | (binders1,res) ->
                let uu____2974 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2974
                then
                  let uu____2977 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____2977 with
                   | (vars,guards,env',decls,uu____2992) ->
                       let fsym =
                         let uu____3002 = varops.fresh "f" in
                         (uu____3002, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____3005 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_3009 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_3009.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_3009.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_3009.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_3009.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_3009.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_3009.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_3009.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_3009.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_3009.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_3009.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_3009.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_3009.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_3009.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_3009.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_3009.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_3009.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_3009.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_3009.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_3009.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_3009.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_3009.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_3009.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_3009.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____3005 with
                        | (pre_opt,res_t) ->
                            let uu____3016 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____3016 with
                             | (res_pred,decls') ->
                                 let uu____3023 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____3030 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____3030, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____3033 =
                                         encode_formula pre env' in
                                       (match uu____3033 with
                                        | (guard,decls0) ->
                                            let uu____3041 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3041, decls0)) in
                                 (match uu____3023 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3049 =
                                          let uu____3055 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3055) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3049 in
                                      let cvars =
                                        let uu____3065 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3065
                                          (FStar_List.filter
                                             (fun uu____3071  ->
                                                match uu____3071 with
                                                | (x,uu____3075) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3086 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3086 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____3091 =
                                             let uu____3092 =
                                               let uu____3096 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3096) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3092 in
                                           (uu____3091,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____3107 =
                                               let uu____3108 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3108 in
                                             varops.mk_unique uu____3107 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____3115 =
                                               FStar_Options.log_queries () in
                                             if uu____3115
                                             then
                                               let uu____3117 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____3117
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3123 =
                                               let uu____3127 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3127) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3123 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3135 =
                                               let uu____3139 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3139,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3135 in
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
                                             let uu____3152 =
                                               let uu____3156 =
                                                 let uu____3157 =
                                                   let uu____3163 =
                                                     let uu____3164 =
                                                       let uu____3167 =
                                                         let uu____3168 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3168 in
                                                       (f_has_t, uu____3167) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3164 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3163) in
                                                 mkForall_fuel uu____3157 in
                                               (uu____3156,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3152 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3181 =
                                               let uu____3185 =
                                                 let uu____3186 =
                                                   let uu____3192 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3192) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3186 in
                                               (uu____3185,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3181 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3206 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3206);
                                            (t1, t_decls)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow" in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None) in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym in
                     let uu____3217 =
                       let uu____3221 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3221,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3217 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3230 =
                       let uu____3234 =
                         let uu____3235 =
                           let uu____3241 =
                             let uu____3242 =
                               let uu____3245 =
                                 let uu____3246 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3246 in
                               (f_has_t, uu____3245) in
                             FStar_SMTEncoding_Util.mkImp uu____3242 in
                           ([[f_has_t]], [fsym], uu____3241) in
                         mkForall_fuel uu____3235 in
                       (uu____3234, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3230 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3260 ->
           let uu____3265 =
             let uu____3268 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3268 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3273;
                 FStar_Syntax_Syntax.pos = uu____3274;
                 FStar_Syntax_Syntax.vars = uu____3275;_} ->
                 let uu____3282 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____3282 with
                  | (b,f1) ->
                      let uu____3296 =
                        let uu____3297 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____3297 in
                      (uu____3296, f1))
             | uu____3302 -> failwith "impossible" in
           (match uu____3265 with
            | (x,f) ->
                let uu____3309 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3309 with
                 | (base_t,decls) ->
                     let uu____3316 = gen_term_var env x in
                     (match uu____3316 with
                      | (x1,xtm,env') ->
                          let uu____3325 = encode_formula f env' in
                          (match uu____3325 with
                           | (refinement,decls') ->
                               let uu____3332 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3332 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3343 =
                                        let uu____3345 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3349 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3345
                                          uu____3349 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3343 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3365  ->
                                              match uu____3365 with
                                              | (y,uu____3369) ->
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
                                    let uu____3388 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3388 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____3393 =
                                           let uu____3394 =
                                             let uu____3398 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3398) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3394 in
                                         (uu____3393,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3410 =
                                             let uu____3411 =
                                               let uu____3412 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3412 in
                                             Prims.strcat module_name
                                               uu____3411 in
                                           varops.mk_unique uu____3410 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives_Native.snd
                                             cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                         let t1 =
                                           let uu____3421 =
                                             let uu____3425 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3425) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3421 in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (FStar_Pervasives_Native.Some
                                                fterm) xtm t1 in
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
                                           let uu____3435 =
                                             let uu____3439 =
                                               let uu____3440 =
                                                 let uu____3446 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3446) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3440 in
                                             (uu____3439,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3435 in
                                         let t_kinding =
                                           let uu____3456 =
                                             let uu____3460 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3460,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3456 in
                                         let t_interp =
                                           let uu____3470 =
                                             let uu____3474 =
                                               let uu____3475 =
                                                 let uu____3481 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3481) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3475 in
                                             let uu____3493 =
                                               let uu____3495 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____3495 in
                                             (uu____3474, uu____3493,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3470 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3500 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3500);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3517 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3517 in
           let uu____3521 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____3521 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3529 =
                    let uu____3533 =
                      let uu____3534 =
                        let uu____3535 =
                          let uu____3536 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3536 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3535 in
                      varops.mk_unique uu____3534 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____3533) in
                  FStar_SMTEncoding_Util.mkAssume uu____3529 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3542 ->
           let uu____3552 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3552 with
            | (head1,args_e) ->
                let uu____3580 =
                  let uu____3588 =
                    let uu____3589 = FStar_Syntax_Subst.compress head1 in
                    uu____3589.FStar_Syntax_Syntax.n in
                  (uu____3588, args_e) in
                (match uu____3580 with
                 | uu____3599 when head_redex env head1 ->
                     let uu____3607 = whnf env t in
                     encode_term uu____3607 env
                 | uu____3608 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____3621;
                       FStar_Syntax_Syntax.pos = uu____3622;
                       FStar_Syntax_Syntax.vars = uu____3623;_},uu____3624),uu____3625::
                    (v1,uu____3627)::(v2,uu____3629)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____3667 = encode_term v1 env in
                     (match uu____3667 with
                      | (v11,decls1) ->
                          let uu____3674 = encode_term v2 env in
                          (match uu____3674 with
                           | (v21,decls2) ->
                               let uu____3681 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3681,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3684::(v1,uu____3686)::(v2,uu____3688)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____3722 = encode_term v1 env in
                     (match uu____3722 with
                      | (v11,decls1) ->
                          let uu____3729 = encode_term v2 env in
                          (match uu____3729 with
                           | (v21,decls2) ->
                               let uu____3736 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3736,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3738) ->
                     let e0 =
                       let uu____3750 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3750 in
                     ((let uu____3756 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3756
                       then
                         let uu____3757 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3757
                       else ());
                      (let e =
                         let uu____3762 =
                           let uu____3763 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3764 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3763
                             uu____3764 in
                         uu____3762 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3773),(arg,uu____3775)::[]) -> encode_term arg env
                 | uu____3793 ->
                     let uu____3801 = encode_args args_e env in
                     (match uu____3801 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3834 = encode_term head1 env in
                            match uu____3834 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____3873 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3873 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3915  ->
                                                 fun uu____3916  ->
                                                   match (uu____3915,
                                                           uu____3916)
                                                   with
                                                   | ((bv,uu____3930),
                                                      (a,uu____3932)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3946 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3946
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3951 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____3951 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3961 =
                                                   let uu____3965 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3970 =
                                                     let uu____3971 =
                                                       let uu____3972 =
                                                         let uu____3973 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3973 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3972 in
                                                     varops.mk_unique
                                                       uu____3971 in
                                                   (uu____3965,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____3970) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3961 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3990 = lookup_free_var_sym env fv in
                            match uu____3990 with
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
                                   FStar_Syntax_Syntax.tk = uu____4013;
                                   FStar_Syntax_Syntax.pos = uu____4014;
                                   FStar_Syntax_Syntax.vars = uu____4015;_},uu____4016)
                                ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____4027;
                                   FStar_Syntax_Syntax.pos = uu____4028;
                                   FStar_Syntax_Syntax.vars = uu____4029;_},uu____4030)
                                ->
                                let uu____4035 =
                                  let uu____4036 =
                                    let uu____4039 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4039
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____4036
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____4035
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4059 =
                                  let uu____4060 =
                                    let uu____4063 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4063
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____4060
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____4059
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4082,(FStar_Util.Inl t1,uu____4084),uu____4085)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4123,(FStar_Util.Inr c,uu____4125),uu____4126)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____4164 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____4184 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4184 in
                               let uu____4185 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4185 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4195;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4196;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4197;_},uu____4198)
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
                                     | uu____4222 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (FStar_Pervasives_Native.Some
                                                (formals, c))
                                         else
                                           encode_partial_app
                                             FStar_Pervasives_Native.None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4267 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4267 with
            | (bs1,body1,opening) ->
                let fallback uu____4282 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____4287 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4287, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4298 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____4298
                  | FStar_Util.Inr (eff,uu____4300) ->
                      let uu____4306 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____4306 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4351 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___136_4352 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___136_4352.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___136_4352.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___136_4352.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___136_4352.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___136_4352.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___136_4352.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___136_4352.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___136_4352.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___136_4352.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___136_4352.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___136_4352.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___136_4352.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___136_4352.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___136_4352.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___136_4352.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___136_4352.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___136_4352.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___136_4352.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___136_4352.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___136_4352.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___136_4352.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___136_4352.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___136_4352.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4351 FStar_Syntax_Syntax.U_unknown in
                        let uu____4353 =
                          let uu____4354 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4354 in
                        FStar_Util.Inl uu____4353
                    | FStar_Util.Inr (eff_name,uu____4361) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4392 =
                        let uu____4393 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4393 in
                      FStar_All.pipe_right uu____4392
                        (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4405 =
                        let uu____4406 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4406
                          FStar_Pervasives_Native.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Parser_Const.effect_Tot_lid
                      then
                        let uu____4414 =
                          let uu____4415 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4415 in
                        FStar_All.pipe_right uu____4414
                          (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Parser_Const.effect_GTot_lid
                        then
                          (let uu____4419 =
                             let uu____4420 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4420 in
                           FStar_All.pipe_right uu____4419
                             (fun _0_33  ->
                                FStar_Pervasives_Native.Some _0_33))
                        else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____4431 =
                         let uu____4432 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4432 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4431);
                      fallback ())
                 | FStar_Pervasives_Native.Some lc ->
                     let lc1 = lc in
                     let uu____4447 =
                       (is_impure lc1) &&
                         (let uu____4448 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4448) in
                     if uu____4447
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4453 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____4453 with
                        | (vars,guards,envbody,decls,uu____4468) ->
                            let uu____4475 =
                              let uu____4483 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4483
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4475 with
                             | (lc2,body2) ->
                                 let uu____4508 = encode_term body2 envbody in
                                 (match uu____4508 with
                                  | (body3,decls') ->
                                      let uu____4515 =
                                        let uu____4520 = codomain_eff lc2 in
                                        match uu____4520 with
                                        | FStar_Pervasives_Native.None  ->
                                            (FStar_Pervasives_Native.None,
                                              [])
                                        | FStar_Pervasives_Native.Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4532 =
                                              encode_term tfun env in
                                            (match uu____4532 with
                                             | (t1,decls1) ->
                                                 ((FStar_Pervasives_Native.Some
                                                     t1), decls1)) in
                                      (match uu____4515 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4551 =
                                               let uu____4557 =
                                                 let uu____4558 =
                                                   let uu____4561 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4561, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4558 in
                                               ([], vars, uu____4557) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4551 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | FStar_Pervasives_Native.None 
                                                 -> cvars
                                             | FStar_Pervasives_Native.Some
                                                 t1 ->
                                                 let uu____4569 =
                                                   let uu____4571 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4571 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4569 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4582 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4582 with
                                            | FStar_Pervasives_Native.Some
                                                cache_entry ->
                                                let uu____4587 =
                                                  let uu____4588 =
                                                    let uu____4592 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4592) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4588 in
                                                (uu____4587,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let uu____4598 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4598 with
                                                 | FStar_Pervasives_Native.Some
                                                     t1 ->
                                                     let decls1 =
                                                       let uu____4605 =
                                                         let uu____4606 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4606 =
                                                           cache_size in
                                                       if uu____4605
                                                       then []
                                                       else
                                                         FStar_List.append
                                                           decls
                                                           (FStar_List.append
                                                              decls' decls'') in
                                                     (t1, decls1)
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let cvar_sorts =
                                                       FStar_List.map
                                                         FStar_Pervasives_Native.snd
                                                         cvars1 in
                                                     let fsym =
                                                       let module_name =
                                                         env.current_module_name in
                                                       let fsym =
                                                         let uu____4617 =
                                                           let uu____4618 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4618 in
                                                         varops.mk_unique
                                                           uu____4617 in
                                                       Prims.strcat
                                                         module_name
                                                         (Prims.strcat "_"
                                                            fsym) in
                                                     let fdecl =
                                                       FStar_SMTEncoding_Term.DeclFun
                                                         (fsym, cvar_sorts,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           FStar_Pervasives_Native.None) in
                                                     let f =
                                                       let uu____4623 =
                                                         let uu____4627 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4627) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4623 in
                                                     let app =
                                                       mk_Apply f vars in
                                                     let typing_f =
                                                       match arrow_t_opt with
                                                       | FStar_Pervasives_Native.None
                                                            -> []
                                                       | FStar_Pervasives_Native.Some
                                                           t1 ->
                                                           let f_has_t =
                                                             FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                               FStar_Pervasives_Native.None
                                                               f t1 in
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym in
                                                           let uu____4639 =
                                                             let uu____4640 =
                                                               let uu____4644
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4644,
                                                                 (FStar_Pervasives_Native.Some
                                                                    a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4640 in
                                                           [uu____4639] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4652 =
                                                         let uu____4656 =
                                                           let uu____4657 =
                                                             let uu____4663 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4663) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4657 in
                                                         (uu____4656,
                                                           (FStar_Pervasives_Native.Some
                                                              a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4652 in
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
                                                     ((let uu____4673 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4673);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4675,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4676;
                          FStar_Syntax_Syntax.lbunivs = uu____4677;
                          FStar_Syntax_Syntax.lbtyp = uu____4678;
                          FStar_Syntax_Syntax.lbeff = uu____4679;
                          FStar_Syntax_Syntax.lbdef = uu____4680;_}::uu____4681),uu____4682)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4700;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4702;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4718 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort,
                   FStar_Pervasives_Native.None) in
             let uu____4731 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4731, [decl_e])))
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
                 (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                   FStar_Pervasives_Native.tuple2)
              ->
              (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____4773 = encode_term e1 env in
              match uu____4773 with
              | (ee1,decls1) ->
                  let uu____4780 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____4780 with
                   | (xs,e21) ->
                       let uu____4794 = FStar_List.hd xs in
                       (match uu____4794 with
                        | (x1,uu____4802) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4804 = encode_body e21 env' in
                            (match uu____4804 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))
and encode_match:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        env_t ->
          (FStar_Syntax_Syntax.term ->
             env_t ->
               (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                 FStar_Pervasives_Native.tuple2)
            ->
            (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
              FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____4826 =
              let uu____4830 =
                let uu____4831 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4831 in
              gen_term_var env uu____4830 in
            match uu____4826 with
            | (scrsym,scr',env1) ->
                let uu____4841 = encode_term e env1 in
                (match uu____4841 with
                 | (scr,decls) ->
                     let uu____4848 =
                       let encode_branch b uu____4864 =
                         match uu____4864 with
                         | (else_case,decls1) ->
                             let uu____4875 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4875 with
                              | (p,w,br) ->
                                  let uu____4896 = encode_pat env1 p in
                                  (match uu____4896 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____4916  ->
                                                   match uu____4916 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____4921 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____4936 =
                                               encode_term w1 env2 in
                                             (match uu____4936 with
                                              | (w2,decls2) ->
                                                  let uu____4944 =
                                                    let uu____4945 =
                                                      let uu____4948 =
                                                        let uu____4949 =
                                                          let uu____4952 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____4952) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____4949 in
                                                      (guard, uu____4948) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____4945 in
                                                  (uu____4944, decls2)) in
                                       (match uu____4921 with
                                        | (guard1,decls2) ->
                                            let uu____4960 =
                                              encode_br br env2 in
                                            (match uu____4960 with
                                             | (br1,decls3) ->
                                                 let uu____4968 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____4968,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4848 with
                      | (match_tm,decls1) ->
                          let uu____4979 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4979, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____5001 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5001
       then
         let uu____5002 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5002
       else ());
      (let uu____5004 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5004 with
       | (vars,pat_term) ->
           let uu____5014 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5037  ->
                     fun v1  ->
                       match uu____5037 with
                       | (env1,vars1) ->
                           let uu____5065 = gen_term_var env1 v1 in
                           (match uu____5065 with
                            | (xx,uu____5077,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____5014 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5124 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5125 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5126 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5132 =
                        let uu____5135 = encode_const c in
                        (scrutinee, uu____5135) in
                      FStar_SMTEncoding_Util.mkEq uu____5132
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5154 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5154 with
                        | (uu____5158,uu____5159::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5161 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5182  ->
                                  match uu____5182 with
                                  | (arg,uu____5188) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5198 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5198)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5218) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5237 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5252 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5274  ->
                                  match uu____5274 with
                                  | (arg,uu____5283) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5293 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5293)) in
                      FStar_All.pipe_right uu____5252 FStar_List.flatten in
                let pat_term1 uu____5309 = encode_term pat_term env1 in
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
      (FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    fun env  ->
      let uu____5316 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5331  ->
                fun uu____5332  ->
                  match (uu____5331, uu____5332) with
                  | ((tms,decls),(t,uu____5352)) ->
                      let uu____5363 = encode_term t env in
                      (match uu____5363 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5316 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5397 = FStar_Syntax_Util.list_elements e in
        match uu____5397 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5412 =
          let uu____5422 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5422 FStar_Syntax_Util.head_and_args in
        match uu____5412 with
        | (head1,args) ->
            let uu____5450 =
              let uu____5458 =
                let uu____5459 = FStar_Syntax_Util.un_uinst head1 in
                uu____5459.FStar_Syntax_Syntax.n in
              (uu____5458, args) in
            (match uu____5450 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5470,uu____5471)::(e,uu____5473)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____5499 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____5526 =
            let uu____5536 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5536 FStar_Syntax_Util.head_and_args in
          match uu____5526 with
          | (head1,args) ->
              let uu____5565 =
                let uu____5573 =
                  let uu____5574 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5574.FStar_Syntax_Syntax.n in
                (uu____5573, args) in
              (match uu____5565 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5587)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____5607 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____5622 = smt_pat_or1 t1 in
            (match uu____5622 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____5635 = list_elements1 e in
                 FStar_All.pipe_right uu____5635
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5646 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5646
                           (FStar_List.map one_pat)))
             | uu____5654 ->
                 let uu____5658 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5658])
        | uu____5674 ->
            let uu____5676 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5676] in
      let uu____5692 =
        let uu____5705 =
          let uu____5706 = FStar_Syntax_Subst.compress t in
          uu____5706.FStar_Syntax_Syntax.n in
        match uu____5705 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5733 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5733 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5762;
                        FStar_Syntax_Syntax.effect_name = uu____5763;
                        FStar_Syntax_Syntax.result_typ = uu____5764;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5766)::(post,uu____5768)::(pats,uu____5770)::[];
                        FStar_Syntax_Syntax.flags = uu____5771;_}
                      ->
                      let uu____5803 = lemma_pats pats in
                      (binders1, pre, post, uu____5803)
                  | uu____5816 -> failwith "impos"))
        | uu____5829 -> failwith "Impos" in
      match uu____5692 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___137_5865 = env in
            {
              bindings = (uu___137_5865.bindings);
              depth = (uu___137_5865.depth);
              tcenv = (uu___137_5865.tcenv);
              warn = (uu___137_5865.warn);
              cache = (uu___137_5865.cache);
              nolabels = (uu___137_5865.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___137_5865.encode_non_total_function_typ);
              current_module_name = (uu___137_5865.current_module_name)
            } in
          let uu____5866 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____5866 with
           | (vars,guards,env2,decls,uu____5881) ->
               let uu____5888 =
                 let uu____5895 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____5917 =
                             let uu____5922 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____5922 FStar_List.unzip in
                           match uu____5917 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____5895 FStar_List.unzip in
               (match uu____5888 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___138_5980 = env2 in
                      {
                        bindings = (uu___138_5980.bindings);
                        depth = (uu___138_5980.depth);
                        tcenv = (uu___138_5980.tcenv);
                        warn = (uu___138_5980.warn);
                        cache = (uu___138_5980.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___138_5980.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___138_5980.encode_non_total_function_typ);
                        current_module_name =
                          (uu___138_5980.current_module_name)
                      } in
                    let uu____5981 =
                      let uu____5984 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____5984 env3 in
                    (match uu____5981 with
                     | (pre1,decls'') ->
                         let uu____5989 =
                           let uu____5992 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____5992 env3 in
                         (match uu____5989 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____5999 =
                                let uu____6000 =
                                  let uu____6006 =
                                    let uu____6007 =
                                      let uu____6010 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6010, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6007 in
                                  (pats, vars, uu____6006) in
                                FStar_SMTEncoding_Util.mkForall uu____6000 in
                              (uu____5999, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6023 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6023
        then
          let uu____6024 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6025 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6024 uu____6025
        else () in
      let enc f r l =
        let uu____6052 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6065 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____6065 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6052 with
        | (decls,args) ->
            let uu____6082 =
              let uu___139_6083 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6083.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6083.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6082, decls) in
      let const_op f r uu____6102 = let uu____6105 = f r in (uu____6105, []) in
      let un_op f l =
        let uu____6121 = FStar_List.hd l in FStar_All.pipe_left f uu____6121 in
      let bin_op f uu___111_6134 =
        match uu___111_6134 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6142 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6169 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6178  ->
                 match uu____6178 with
                 | (t,uu____6186) ->
                     let uu____6187 = encode_formula t env in
                     (match uu____6187 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6169 with
        | (decls,phis) ->
            let uu____6204 =
              let uu___140_6205 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_6205.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_6205.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6204, decls) in
      let eq_op r uu___112_6221 =
        match uu___112_6221 with
        | uu____6224::e1::e2::[] ->
            let uu____6255 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6255 r [e1; e2]
        | uu____6274::uu____6275::e1::e2::[] ->
            let uu____6314 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6314 r [e1; e2]
        | l ->
            let uu____6334 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6334 r l in
      let mk_imp1 r uu___113_6353 =
        match uu___113_6353 with
        | (lhs,uu____6357)::(rhs,uu____6359)::[] ->
            let uu____6380 = encode_formula rhs env in
            (match uu____6380 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6389) ->
                      (l1, decls1)
                  | uu____6392 ->
                      let uu____6393 = encode_formula lhs env in
                      (match uu____6393 with
                       | (l2,decls2) ->
                           let uu____6400 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6400, (FStar_List.append decls1 decls2)))))
        | uu____6402 -> failwith "impossible" in
      let mk_ite r uu___114_6417 =
        match uu___114_6417 with
        | (guard,uu____6421)::(_then,uu____6423)::(_else,uu____6425)::[] ->
            let uu____6454 = encode_formula guard env in
            (match uu____6454 with
             | (g,decls1) ->
                 let uu____6461 = encode_formula _then env in
                 (match uu____6461 with
                  | (t,decls2) ->
                      let uu____6468 = encode_formula _else env in
                      (match uu____6468 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6477 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6496 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6496 in
      let connectives =
        let uu____6508 =
          let uu____6517 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____6517) in
        let uu____6530 =
          let uu____6540 =
            let uu____6549 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____6549) in
          let uu____6562 =
            let uu____6572 =
              let uu____6582 =
                let uu____6591 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____6591) in
              let uu____6604 =
                let uu____6614 =
                  let uu____6624 =
                    let uu____6633 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____6633) in
                  [uu____6624;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____6614 in
              uu____6582 :: uu____6604 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____6572 in
          uu____6540 :: uu____6562 in
        uu____6508 :: uu____6530 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6795 = encode_formula phi' env in
            (match uu____6795 with
             | (phi2,decls) ->
                 let uu____6802 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6802, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6803 ->
            let uu____6808 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6808 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6837 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6837 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6845;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6847;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6863 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6863 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6895::(x,uu____6897)::(t,uu____6899)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____6933 = encode_term x env in
                 (match uu____6933 with
                  | (x1,decls) ->
                      let uu____6940 = encode_term t env in
                      (match uu____6940 with
                       | (t1,decls') ->
                           let uu____6947 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6947, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6951)::(msg,uu____6953)::(phi2,uu____6955)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____6989 =
                   let uu____6992 =
                     let uu____6993 = FStar_Syntax_Subst.compress r in
                     uu____6993.FStar_Syntax_Syntax.n in
                   let uu____6996 =
                     let uu____6997 = FStar_Syntax_Subst.compress msg in
                     uu____6997.FStar_Syntax_Syntax.n in
                   (uu____6992, uu____6996) in
                 (match uu____6989 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7004))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   (s, r1, false)))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____7018 -> fallback phi2)
             | uu____7021 when head_redex env head2 ->
                 let uu____7029 = whnf env phi1 in
                 encode_formula uu____7029 env
             | uu____7030 ->
                 let uu____7038 = encode_term phi1 env in
                 (match uu____7038 with
                  | (tt,decls) ->
                      let uu____7045 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___141_7046 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___141_7046.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___141_7046.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7045, decls)))
        | uu____7049 ->
            let uu____7050 = encode_term phi1 env in
            (match uu____7050 with
             | (tt,decls) ->
                 let uu____7057 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___142_7058 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___142_7058.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___142_7058.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7057, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7085 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____7085 with
        | (vars,guards,env2,decls,uu____7107) ->
            let uu____7114 =
              let uu____7121 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7144 =
                          let uu____7149 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7163  ->
                                    match uu____7163 with
                                    | (t,uu____7169) ->
                                        encode_term t
                                          (let uu___143_7170 = env2 in
                                           {
                                             bindings =
                                               (uu___143_7170.bindings);
                                             depth = (uu___143_7170.depth);
                                             tcenv = (uu___143_7170.tcenv);
                                             warn = (uu___143_7170.warn);
                                             cache = (uu___143_7170.cache);
                                             nolabels =
                                               (uu___143_7170.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___143_7170.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___143_7170.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7149 FStar_List.unzip in
                        match uu____7144 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7121 FStar_List.unzip in
            (match uu____7114 with
             | (pats,decls') ->
                 let uu____7222 = encode_formula body env2 in
                 (match uu____7222 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7241;
                             FStar_SMTEncoding_Term.rng = uu____7242;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____7250 -> guards in
                      let uu____7253 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7253, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7287  ->
                   match uu____7287 with
                   | (x,uu____7291) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7297 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7303 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7303) uu____7297 tl1 in
             let uu____7305 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7317  ->
                       match uu____7317 with
                       | (b,uu____7321) ->
                           let uu____7322 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7322)) in
             (match uu____7305 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____7326) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7336 =
                    let uu____7337 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7337 in
                  FStar_Errors.warn pos uu____7336) in
       let uu____7338 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7338 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____7344 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7380  ->
                     match uu____7380 with
                     | (l,uu____7390) -> FStar_Ident.lid_equals op l)) in
           (match uu____7344 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____7413,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7442 = encode_q_body env vars pats body in
             match uu____7442 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7468 =
                     let uu____7474 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7474) in
                   FStar_SMTEncoding_Term.mkForall uu____7468
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7486 = encode_q_body env vars pats body in
             match uu____7486 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7511 =
                   let uu____7512 =
                     let uu____7518 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7518) in
                   FStar_SMTEncoding_Term.mkExists uu____7512
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7511, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2;
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7572 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7572 with
  | (asym,a) ->
      let uu____7577 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7577 with
       | (xsym,x) ->
           let uu____7582 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7582 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7612 =
                      let uu____7618 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____7618, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7612 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____7633 =
                      let uu____7637 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7637) in
                    FStar_SMTEncoding_Util.mkApp uu____7633 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7645 =
                    let uu____7647 =
                      let uu____7649 =
                        let uu____7651 =
                          let uu____7652 =
                            let uu____7656 =
                              let uu____7657 =
                                let uu____7663 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7663) in
                              FStar_SMTEncoding_Util.mkForall uu____7657 in
                            (uu____7656, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7652 in
                        let uu____7672 =
                          let uu____7674 =
                            let uu____7675 =
                              let uu____7679 =
                                let uu____7680 =
                                  let uu____7686 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7686) in
                                FStar_SMTEncoding_Util.mkForall uu____7680 in
                              (uu____7679,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7675 in
                          [uu____7674] in
                        uu____7651 :: uu____7672 in
                      xtok_decl :: uu____7649 in
                    xname_decl :: uu____7647 in
                  (xtok1, uu____7645) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7735 =
                    let uu____7743 =
                      let uu____7749 =
                        let uu____7750 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7750 in
                      quant axy uu____7749 in
                    (FStar_Parser_Const.op_Eq, uu____7743) in
                  let uu____7756 =
                    let uu____7765 =
                      let uu____7773 =
                        let uu____7779 =
                          let uu____7780 =
                            let uu____7781 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7781 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7780 in
                        quant axy uu____7779 in
                      (FStar_Parser_Const.op_notEq, uu____7773) in
                    let uu____7787 =
                      let uu____7796 =
                        let uu____7804 =
                          let uu____7810 =
                            let uu____7811 =
                              let uu____7812 =
                                let uu____7815 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7816 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7815, uu____7816) in
                              FStar_SMTEncoding_Util.mkLT uu____7812 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7811 in
                          quant xy uu____7810 in
                        (FStar_Parser_Const.op_LT, uu____7804) in
                      let uu____7822 =
                        let uu____7831 =
                          let uu____7839 =
                            let uu____7845 =
                              let uu____7846 =
                                let uu____7847 =
                                  let uu____7850 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7851 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7850, uu____7851) in
                                FStar_SMTEncoding_Util.mkLTE uu____7847 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7846 in
                            quant xy uu____7845 in
                          (FStar_Parser_Const.op_LTE, uu____7839) in
                        let uu____7857 =
                          let uu____7866 =
                            let uu____7874 =
                              let uu____7880 =
                                let uu____7881 =
                                  let uu____7882 =
                                    let uu____7885 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7886 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7885, uu____7886) in
                                  FStar_SMTEncoding_Util.mkGT uu____7882 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7881 in
                              quant xy uu____7880 in
                            (FStar_Parser_Const.op_GT, uu____7874) in
                          let uu____7892 =
                            let uu____7901 =
                              let uu____7909 =
                                let uu____7915 =
                                  let uu____7916 =
                                    let uu____7917 =
                                      let uu____7920 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7921 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7920, uu____7921) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7917 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7916 in
                                quant xy uu____7915 in
                              (FStar_Parser_Const.op_GTE, uu____7909) in
                            let uu____7927 =
                              let uu____7936 =
                                let uu____7944 =
                                  let uu____7950 =
                                    let uu____7951 =
                                      let uu____7952 =
                                        let uu____7955 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7956 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7955, uu____7956) in
                                      FStar_SMTEncoding_Util.mkSub uu____7952 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7951 in
                                  quant xy uu____7950 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____7944) in
                              let uu____7962 =
                                let uu____7971 =
                                  let uu____7979 =
                                    let uu____7985 =
                                      let uu____7986 =
                                        let uu____7987 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7987 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7986 in
                                    quant qx uu____7985 in
                                  (FStar_Parser_Const.op_Minus, uu____7979) in
                                let uu____7993 =
                                  let uu____8002 =
                                    let uu____8010 =
                                      let uu____8016 =
                                        let uu____8017 =
                                          let uu____8018 =
                                            let uu____8021 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8022 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8021, uu____8022) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8018 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8017 in
                                      quant xy uu____8016 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____8010) in
                                  let uu____8028 =
                                    let uu____8037 =
                                      let uu____8045 =
                                        let uu____8051 =
                                          let uu____8052 =
                                            let uu____8053 =
                                              let uu____8056 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8057 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8056, uu____8057) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8053 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8052 in
                                        quant xy uu____8051 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____8045) in
                                    let uu____8063 =
                                      let uu____8072 =
                                        let uu____8080 =
                                          let uu____8086 =
                                            let uu____8087 =
                                              let uu____8088 =
                                                let uu____8091 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8092 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8091, uu____8092) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8088 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8087 in
                                          quant xy uu____8086 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____8080) in
                                      let uu____8098 =
                                        let uu____8107 =
                                          let uu____8115 =
                                            let uu____8121 =
                                              let uu____8122 =
                                                let uu____8123 =
                                                  let uu____8126 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8127 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8126, uu____8127) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8123 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8122 in
                                            quant xy uu____8121 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____8115) in
                                        let uu____8133 =
                                          let uu____8142 =
                                            let uu____8150 =
                                              let uu____8156 =
                                                let uu____8157 =
                                                  let uu____8158 =
                                                    let uu____8161 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8162 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8161, uu____8162) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8158 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8157 in
                                              quant xy uu____8156 in
                                            (FStar_Parser_Const.op_And,
                                              uu____8150) in
                                          let uu____8168 =
                                            let uu____8177 =
                                              let uu____8185 =
                                                let uu____8191 =
                                                  let uu____8192 =
                                                    let uu____8193 =
                                                      let uu____8196 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8197 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8196,
                                                        uu____8197) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8193 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8192 in
                                                quant xy uu____8191 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____8185) in
                                            let uu____8203 =
                                              let uu____8212 =
                                                let uu____8220 =
                                                  let uu____8226 =
                                                    let uu____8227 =
                                                      let uu____8228 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8228 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8227 in
                                                  quant qx uu____8226 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____8220) in
                                              [uu____8212] in
                                            uu____8177 :: uu____8203 in
                                          uu____8142 :: uu____8168 in
                                        uu____8107 :: uu____8133 in
                                      uu____8072 :: uu____8098 in
                                    uu____8037 :: uu____8063 in
                                  uu____8002 :: uu____8028 in
                                uu____7971 :: uu____7993 in
                              uu____7936 :: uu____7962 in
                            uu____7901 :: uu____7927 in
                          uu____7866 :: uu____7892 in
                        uu____7831 :: uu____7857 in
                      uu____7796 :: uu____7822 in
                    uu____7765 :: uu____7787 in
                  uu____7735 :: uu____7756 in
                let mk1 l v1 =
                  let uu____8356 =
                    let uu____8361 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8393  ->
                              match uu____8393 with
                              | (l',uu____8402) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8361
                      (FStar_Option.map
                         (fun uu____8435  ->
                            match uu____8435 with | (uu____8446,b) -> b v1)) in
                  FStar_All.pipe_right uu____8356 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8487  ->
                          match uu____8487 with
                          | (l',uu____8496) -> FStar_Ident.lid_equals l l')) in
                { mk = mk1; is }))
let pretype_axiom:
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string,FStar_SMTEncoding_Term.sort)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____8522 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8522 with
        | (xxsym,xx) ->
            let uu____8527 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8527 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8535 =
                   let uu____8539 =
                     let uu____8540 =
                       let uu____8546 =
                         let uu____8547 =
                           let uu____8550 =
                             let uu____8551 =
                               let uu____8554 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8554) in
                             FStar_SMTEncoding_Util.mkEq uu____8551 in
                           (xx_has_type, uu____8550) in
                         FStar_SMTEncoding_Util.mkImp uu____8547 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8546) in
                     FStar_SMTEncoding_Util.mkForall uu____8540 in
                   let uu____8567 =
                     let uu____8568 =
                       let uu____8569 =
                         let uu____8570 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8570 in
                       Prims.strcat module_name uu____8569 in
                     varops.mk_unique uu____8568 in
                   (uu____8539, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____8567) in
                 FStar_SMTEncoding_Util.mkAssume uu____8535)
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
    let uu____8600 =
      let uu____8601 =
        let uu____8605 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8605, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8601 in
    let uu____8607 =
      let uu____8609 =
        let uu____8610 =
          let uu____8614 =
            let uu____8615 =
              let uu____8621 =
                let uu____8622 =
                  let uu____8625 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8625) in
                FStar_SMTEncoding_Util.mkImp uu____8622 in
              ([[typing_pred]], [xx], uu____8621) in
            mkForall_fuel uu____8615 in
          (uu____8614, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8610 in
      [uu____8609] in
    uu____8600 :: uu____8607 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8653 =
      let uu____8654 =
        let uu____8658 =
          let uu____8659 =
            let uu____8665 =
              let uu____8668 =
                let uu____8670 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8670] in
              [uu____8668] in
            let uu____8673 =
              let uu____8674 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8674 tt in
            (uu____8665, [bb], uu____8673) in
          FStar_SMTEncoding_Util.mkForall uu____8659 in
        (uu____8658, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8654 in
    let uu____8685 =
      let uu____8687 =
        let uu____8688 =
          let uu____8692 =
            let uu____8693 =
              let uu____8699 =
                let uu____8700 =
                  let uu____8703 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8703) in
                FStar_SMTEncoding_Util.mkImp uu____8700 in
              ([[typing_pred]], [xx], uu____8699) in
            mkForall_fuel uu____8693 in
          (uu____8692, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8688 in
      [uu____8687] in
    uu____8653 :: uu____8685 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8737 =
        let uu____8738 =
          let uu____8742 =
            let uu____8744 =
              let uu____8746 =
                let uu____8748 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8749 =
                  let uu____8751 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8751] in
                uu____8748 :: uu____8749 in
              tt :: uu____8746 in
            tt :: uu____8744 in
          ("Prims.Precedes", uu____8742) in
        FStar_SMTEncoding_Util.mkApp uu____8738 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8737 in
    let precedes_y_x =
      let uu____8754 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8754 in
    let uu____8756 =
      let uu____8757 =
        let uu____8761 =
          let uu____8762 =
            let uu____8768 =
              let uu____8771 =
                let uu____8773 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8773] in
              [uu____8771] in
            let uu____8776 =
              let uu____8777 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8777 tt in
            (uu____8768, [bb], uu____8776) in
          FStar_SMTEncoding_Util.mkForall uu____8762 in
        (uu____8761, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8757 in
    let uu____8788 =
      let uu____8790 =
        let uu____8791 =
          let uu____8795 =
            let uu____8796 =
              let uu____8802 =
                let uu____8803 =
                  let uu____8806 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8806) in
                FStar_SMTEncoding_Util.mkImp uu____8803 in
              ([[typing_pred]], [xx], uu____8802) in
            mkForall_fuel uu____8796 in
          (uu____8795, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8791 in
      let uu____8819 =
        let uu____8821 =
          let uu____8822 =
            let uu____8826 =
              let uu____8827 =
                let uu____8833 =
                  let uu____8834 =
                    let uu____8837 =
                      let uu____8838 =
                        let uu____8840 =
                          let uu____8842 =
                            let uu____8844 =
                              let uu____8845 =
                                let uu____8848 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8849 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8848, uu____8849) in
                              FStar_SMTEncoding_Util.mkGT uu____8845 in
                            let uu____8850 =
                              let uu____8852 =
                                let uu____8853 =
                                  let uu____8856 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8857 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8856, uu____8857) in
                                FStar_SMTEncoding_Util.mkGTE uu____8853 in
                              let uu____8858 =
                                let uu____8860 =
                                  let uu____8861 =
                                    let uu____8864 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8865 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8864, uu____8865) in
                                  FStar_SMTEncoding_Util.mkLT uu____8861 in
                                [uu____8860] in
                              uu____8852 :: uu____8858 in
                            uu____8844 :: uu____8850 in
                          typing_pred_y :: uu____8842 in
                        typing_pred :: uu____8840 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8838 in
                    (uu____8837, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8834 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8833) in
              mkForall_fuel uu____8827 in
            (uu____8826,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8822 in
        [uu____8821] in
      uu____8790 :: uu____8819 in
    uu____8756 :: uu____8788 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8895 =
      let uu____8896 =
        let uu____8900 =
          let uu____8901 =
            let uu____8907 =
              let uu____8910 =
                let uu____8912 = FStar_SMTEncoding_Term.boxString b in
                [uu____8912] in
              [uu____8910] in
            let uu____8915 =
              let uu____8916 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8916 tt in
            (uu____8907, [bb], uu____8915) in
          FStar_SMTEncoding_Util.mkForall uu____8901 in
        (uu____8900, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8896 in
    let uu____8927 =
      let uu____8929 =
        let uu____8930 =
          let uu____8934 =
            let uu____8935 =
              let uu____8941 =
                let uu____8942 =
                  let uu____8945 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8945) in
                FStar_SMTEncoding_Util.mkImp uu____8942 in
              ([[typing_pred]], [xx], uu____8941) in
            mkForall_fuel uu____8935 in
          (uu____8934, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8930 in
      [uu____8929] in
    uu____8895 :: uu____8927 in
  let mk_ref1 env reft_name uu____8967 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8978 =
        let uu____8982 =
          let uu____8984 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8984] in
        (reft_name, uu____8982) in
      FStar_SMTEncoding_Util.mkApp uu____8978 in
    let refb =
      let uu____8987 =
        let uu____8991 =
          let uu____8993 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8993] in
        (reft_name, uu____8991) in
      FStar_SMTEncoding_Util.mkApp uu____8987 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8997 =
      let uu____8998 =
        let uu____9002 =
          let uu____9003 =
            let uu____9009 =
              let uu____9010 =
                let uu____9013 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9013) in
              FStar_SMTEncoding_Util.mkImp uu____9010 in
            ([[typing_pred]], [xx; aa], uu____9009) in
          mkForall_fuel uu____9003 in
        (uu____9002, (FStar_Pervasives_Native.Some "ref inversion"),
          "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____8998 in
    [uu____8997] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9053 =
      let uu____9054 =
        let uu____9058 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9058, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9054 in
    [uu____9053] in
  let mk_and_interp env conj uu____9069 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9086 =
      let uu____9087 =
        let uu____9091 =
          let uu____9092 =
            let uu____9098 =
              let uu____9099 =
                let uu____9102 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9102, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9099 in
            ([[l_and_a_b]], [aa; bb], uu____9098) in
          FStar_SMTEncoding_Util.mkForall uu____9092 in
        (uu____9091, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9087 in
    [uu____9086] in
  let mk_or_interp env disj uu____9126 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9143 =
      let uu____9144 =
        let uu____9148 =
          let uu____9149 =
            let uu____9155 =
              let uu____9156 =
                let uu____9159 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9159, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9156 in
            ([[l_or_a_b]], [aa; bb], uu____9155) in
          FStar_SMTEncoding_Util.mkForall uu____9149 in
        (uu____9148, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9144 in
    [uu____9143] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9200 =
      let uu____9201 =
        let uu____9205 =
          let uu____9206 =
            let uu____9212 =
              let uu____9213 =
                let uu____9216 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9216, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9213 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9212) in
          FStar_SMTEncoding_Util.mkForall uu____9206 in
        (uu____9205, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9201 in
    [uu____9200] in
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
    let uu____9263 =
      let uu____9264 =
        let uu____9268 =
          let uu____9269 =
            let uu____9275 =
              let uu____9276 =
                let uu____9279 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9279, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9276 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9275) in
          FStar_SMTEncoding_Util.mkForall uu____9269 in
        (uu____9268, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9264 in
    [uu____9263] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9324 =
      let uu____9325 =
        let uu____9329 =
          let uu____9330 =
            let uu____9336 =
              let uu____9337 =
                let uu____9340 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9340, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9337 in
            ([[l_imp_a_b]], [aa; bb], uu____9336) in
          FStar_SMTEncoding_Util.mkForall uu____9330 in
        (uu____9329, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9325 in
    [uu____9324] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9381 =
      let uu____9382 =
        let uu____9386 =
          let uu____9387 =
            let uu____9393 =
              let uu____9394 =
                let uu____9397 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9397, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9394 in
            ([[l_iff_a_b]], [aa; bb], uu____9393) in
          FStar_SMTEncoding_Util.mkForall uu____9387 in
        (uu____9386, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9382 in
    [uu____9381] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9431 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9431 in
    let uu____9433 =
      let uu____9434 =
        let uu____9438 =
          let uu____9439 =
            let uu____9445 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9445) in
          FStar_SMTEncoding_Util.mkForall uu____9439 in
        (uu____9438, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9434 in
    [uu____9433] in
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
      let uu____9485 =
        let uu____9489 =
          let uu____9491 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9491] in
        ("Valid", uu____9489) in
      FStar_SMTEncoding_Util.mkApp uu____9485 in
    let uu____9493 =
      let uu____9494 =
        let uu____9498 =
          let uu____9499 =
            let uu____9505 =
              let uu____9506 =
                let uu____9509 =
                  let uu____9510 =
                    let uu____9516 =
                      let uu____9519 =
                        let uu____9521 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9521] in
                      [uu____9519] in
                    let uu____9524 =
                      let uu____9525 =
                        let uu____9528 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9528, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9525 in
                    (uu____9516, [xx1], uu____9524) in
                  FStar_SMTEncoding_Util.mkForall uu____9510 in
                (uu____9509, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9506 in
            ([[l_forall_a_b]], [aa; bb], uu____9505) in
          FStar_SMTEncoding_Util.mkForall uu____9499 in
        (uu____9498, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9494 in
    [uu____9493] in
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
      let uu____9579 =
        let uu____9583 =
          let uu____9585 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9585] in
        ("Valid", uu____9583) in
      FStar_SMTEncoding_Util.mkApp uu____9579 in
    let uu____9587 =
      let uu____9588 =
        let uu____9592 =
          let uu____9593 =
            let uu____9599 =
              let uu____9600 =
                let uu____9603 =
                  let uu____9604 =
                    let uu____9610 =
                      let uu____9613 =
                        let uu____9615 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9615] in
                      [uu____9613] in
                    let uu____9618 =
                      let uu____9619 =
                        let uu____9622 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9622, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9619 in
                    (uu____9610, [xx1], uu____9618) in
                  FStar_SMTEncoding_Util.mkExists uu____9604 in
                (uu____9603, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9600 in
            ([[l_exists_a_b]], [aa; bb], uu____9599) in
          FStar_SMTEncoding_Util.mkForall uu____9593 in
        (uu____9592, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9588 in
    [uu____9587] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9658 =
      let uu____9659 =
        let uu____9663 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9664 = varops.mk_unique "typing_range_const" in
        (uu____9663, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____9664) in
      FStar_SMTEncoding_Util.mkAssume uu____9659 in
    [uu____9658] in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
    (FStar_Parser_Const.string_lid, mk_str);
    (FStar_Parser_Const.ref_lid, mk_ref1);
    (FStar_Parser_Const.true_lid, mk_true_interp);
    (FStar_Parser_Const.false_lid, mk_false_interp);
    (FStar_Parser_Const.and_lid, mk_and_interp);
    (FStar_Parser_Const.or_lid, mk_or_interp);
    (FStar_Parser_Const.eq2_lid, mk_eq2_interp);
    (FStar_Parser_Const.eq3_lid, mk_eq3_interp);
    (FStar_Parser_Const.imp_lid, mk_imp_interp);
    (FStar_Parser_Const.iff_lid, mk_iff_interp);
    (FStar_Parser_Const.not_lid, mk_not_interp);
    (FStar_Parser_Const.forall_lid, mk_forall_interp);
    (FStar_Parser_Const.exists_lid, mk_exists_interp);
    (FStar_Parser_Const.range_lid, mk_range_interp)] in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____9926 =
            FStar_Util.find_opt
              (fun uu____9944  ->
                 match uu____9944 with
                 | (l,uu____9954) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9926 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____9976,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10013 = encode_function_type_as_formula t env in
        match uu____10013 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form,
                   (FStar_Pervasives_Native.Some
                      (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
let encode_free_var:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list,env_t)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun fv  ->
      fun tt  ->
        fun t_norm  ->
          fun quals  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let uu____10045 =
              (let uu____10046 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10046) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10045
            then
              let uu____10050 = new_term_constant_and_tok_from_lid env lid in
              match uu____10050 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10062 =
                      let uu____10063 = FStar_Syntax_Subst.compress t_norm in
                      uu____10063.FStar_Syntax_Syntax.n in
                    match uu____10062 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10068) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10085  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10088 -> [] in
                  let d =
                    FStar_SMTEncoding_Term.DeclFun
                      (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Uninterpreted function symbol for impure function")) in
                  let dd =
                    FStar_SMTEncoding_Term.DeclFun
                      (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Uninterpreted name for impure function")) in
                  ([d; dd], env1)
            else
              (let uu____10097 = prims.is lid in
               if uu____10097
               then
                 let vname = varops.new_fvar lid in
                 let uu____10102 = prims.mk lid vname in
                 match uu____10102 with
                 | (tok,definition) ->
                     let env1 =
                       push_free_var env lid vname
                         (FStar_Pervasives_Native.Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10117 =
                    let uu____10123 = curried_arrow_formals_comp t_norm in
                    match uu____10123 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10134 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10134
                          then
                            let uu____10135 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___144_10136 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___144_10136.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___144_10136.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___144_10136.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___144_10136.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___144_10136.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___144_10136.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___144_10136.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___144_10136.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___144_10136.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___144_10136.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___144_10136.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___144_10136.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___144_10136.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___144_10136.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___144_10136.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___144_10136.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___144_10136.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___144_10136.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___144_10136.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___144_10136.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___144_10136.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___144_10136.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___144_10136.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10135
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10143 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10143)
                        else
                          (args,
                            (FStar_Pervasives_Native.None,
                              (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10117 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10170 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10170 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10183 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10207  ->
                                     match uu___115_10207 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10210 =
                                           FStar_Util.prefix vars in
                                         (match uu____10210 with
                                          | (uu____10221,(xxsym,uu____10223))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10233 =
                                                let uu____10234 =
                                                  let uu____10238 =
                                                    let uu____10239 =
                                                      let uu____10245 =
                                                        let uu____10246 =
                                                          let uu____10249 =
                                                            let uu____10250 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10250 in
                                                          (vapp, uu____10249) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10246 in
                                                      ([[vapp]], vars,
                                                        uu____10245) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10239 in
                                                  (uu____10238,
                                                    (FStar_Pervasives_Native.Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10234 in
                                              [uu____10233])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10261 =
                                           FStar_Util.prefix vars in
                                         (match uu____10261 with
                                          | (uu____10272,(xxsym,uu____10274))
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
                                              let uu____10288 =
                                                let uu____10289 =
                                                  let uu____10293 =
                                                    let uu____10294 =
                                                      let uu____10300 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10300) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10294 in
                                                  (uu____10293,
                                                    (FStar_Pervasives_Native.Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10289 in
                                              [uu____10288])
                                     | uu____10309 -> [])) in
                           let uu____10310 =
                             encode_binders FStar_Pervasives_Native.None
                               formals env1 in
                           (match uu____10310 with
                            | (vars,guards,env',decls1,uu____10326) ->
                                let uu____10333 =
                                  match pre_opt with
                                  | FStar_Pervasives_Native.None  ->
                                      let uu____10338 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10338, decls1)
                                  | FStar_Pervasives_Native.Some p ->
                                      let uu____10340 = encode_formula p env' in
                                      (match uu____10340 with
                                       | (g,ds) ->
                                           let uu____10347 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10347,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10333 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10356 =
                                         let uu____10360 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10360) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10356 in
                                     let uu____10365 =
                                       let vname_decl =
                                         let uu____10370 =
                                           let uu____10376 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10381  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10376,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             FStar_Pervasives_Native.None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10370 in
                                       let uu____10386 =
                                         let env2 =
                                           let uu___145_10390 = env1 in
                                           {
                                             bindings =
                                               (uu___145_10390.bindings);
                                             depth = (uu___145_10390.depth);
                                             tcenv = (uu___145_10390.tcenv);
                                             warn = (uu___145_10390.warn);
                                             cache = (uu___145_10390.cache);
                                             nolabels =
                                               (uu___145_10390.nolabels);
                                             use_zfuel_name =
                                               (uu___145_10390.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___145_10390.current_module_name)
                                           } in
                                         let uu____10391 =
                                           let uu____10392 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10392 in
                                         if uu____10391
                                         then
                                           encode_term_pred
                                             FStar_Pervasives_Native.None tt
                                             env2 vtok_tm
                                         else
                                           encode_term_pred
                                             FStar_Pervasives_Native.None
                                             t_norm env2 vtok_tm in
                                       match uu____10386 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10402::uu____10403 ->
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
                                                   let uu____10426 =
                                                     let uu____10432 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10432) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10426 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10446 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10448 =
                                             match formals with
                                             | [] ->
                                                 let uu____10457 =
                                                   let uu____10458 =
                                                     let uu____10460 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          FStar_Pervasives_Native.Some
                                                            _0_34)
                                                       uu____10460 in
                                                   push_free_var env1 lid
                                                     vname uu____10458 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10457)
                                             | uu____10463 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None) in
                                                 let vtok_fresh =
                                                   let uu____10468 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10468 in
                                                 let name_tok_corr =
                                                   let uu____10470 =
                                                     let uu____10474 =
                                                       let uu____10475 =
                                                         let uu____10481 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10481) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10475 in
                                                     (uu____10474,
                                                       (FStar_Pervasives_Native.Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10470 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10448 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10365 with
                                      | (decls2,env2) ->
                                          let uu____10505 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10510 =
                                              encode_term res_t1 env' in
                                            match uu____10510 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10518 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10518,
                                                  decls) in
                                          (match uu____10505 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10526 =
                                                   let uu____10530 =
                                                     let uu____10531 =
                                                       let uu____10537 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10537) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10531 in
                                                   (uu____10530,
                                                     (FStar_Pervasives_Native.Some
                                                        "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10526 in
                                               let freshness =
                                                 let uu____10546 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10546
                                                 then
                                                   let uu____10549 =
                                                     let uu____10550 =
                                                       let uu____10556 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.snd) in
                                                       let uu____10562 =
                                                         varops.next_id () in
                                                       (vname, uu____10556,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10562) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10550 in
                                                   let uu____10564 =
                                                     let uu____10566 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10566] in
                                                   uu____10549 :: uu____10564
                                                 else [] in
                                               let g =
                                                 let uu____10570 =
                                                   let uu____10572 =
                                                     let uu____10574 =
                                                       let uu____10576 =
                                                         let uu____10578 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10578 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10576 in
                                                     FStar_List.append decls3
                                                       uu____10574 in
                                                   FStar_List.append decls2
                                                     uu____10572 in
                                                 FStar_List.append decls11
                                                   uu____10570 in
                                               (g, env2))))))))
let declare_top_level_let:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string,FStar_SMTEncoding_Term.term
                           FStar_Pervasives_Native.option)
             FStar_Pervasives_Native.tuple2,FStar_SMTEncoding_Term.decl
                                              Prims.list,env_t)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____10600 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10600 with
          | FStar_Pervasives_Native.None  ->
              let uu____10623 = encode_free_var env x t t_norm [] in
              (match uu____10623 with
               | (decls,env1) ->
                   let uu____10638 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10638 with
                    | (n1,x',uu____10657) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____10669) ->
              ((n1, x1), [], env)
let encode_top_level_val:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          (FStar_SMTEncoding_Term.decl Prims.list,env_t)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      fun t  ->
        fun quals  ->
          let tt = norm env t in
          let uu____10702 = encode_free_var env lid t tt quals in
          match uu____10702 with
          | (decls,env1) ->
              let uu____10713 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10713
              then
                let uu____10717 =
                  let uu____10719 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10719 in
                (uu____10717, env1)
              else (decls, env1)
let encode_top_level_vals:
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____10747  ->
                fun lb  ->
                  match uu____10747 with
                  | (decls,env1) ->
                      let uu____10759 =
                        let uu____10763 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10763
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10759 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10777 = FStar_Syntax_Util.head_and_args t in
    match uu____10777 with
    | (hd1,args) ->
        let uu____10803 =
          let uu____10804 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10804.FStar_Syntax_Syntax.n in
        (match uu____10803 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10808,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10821 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____10836  ->
      fun quals  ->
        match uu____10836 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10885 = FStar_Util.first_N nbinders formals in
              match uu____10885 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10925  ->
                         fun uu____10926  ->
                           match (uu____10925, uu____10926) with
                           | ((formal,uu____10936),(binder,uu____10938)) ->
                               let uu____10943 =
                                 let uu____10948 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10948) in
                               FStar_Syntax_Syntax.NT uu____10943) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10953 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10967  ->
                              match uu____10967 with
                              | (x,i) ->
                                  let uu____10974 =
                                    let uu___146_10975 = x in
                                    let uu____10976 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___146_10975.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___146_10975.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10976
                                    } in
                                  (uu____10974, i))) in
                    FStar_All.pipe_right uu____10953
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10988 =
                      let uu____10990 =
                        let uu____10991 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10991.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left
                        (fun _0_35  -> FStar_Pervasives_Native.Some _0_35)
                        uu____10990 in
                    let uu____10995 =
                      let uu____10996 = FStar_Syntax_Subst.compress body in
                      let uu____10997 =
                        let uu____10998 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____10998 in
                      FStar_Syntax_Syntax.extend_app_n uu____10996
                        uu____10997 in
                    uu____10995 uu____10988 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11040 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11040
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___147_11041 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___147_11041.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___147_11041.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___147_11041.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___147_11041.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___147_11041.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___147_11041.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___147_11041.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___147_11041.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___147_11041.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___147_11041.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___147_11041.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___147_11041.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___147_11041.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___147_11041.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___147_11041.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___147_11041.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___147_11041.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___147_11041.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___147_11041.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___147_11041.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___147_11041.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___147_11041.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___147_11041.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11062 = FStar_Syntax_Util.abs_formals e in
                match uu____11062 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11111::uu____11112 ->
                         let uu____11120 =
                           let uu____11121 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11121.FStar_Syntax_Syntax.n in
                         (match uu____11120 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11148 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11148 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11174 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11174
                                   then
                                     let uu____11192 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11192 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11238  ->
                                                   fun uu____11239  ->
                                                     match (uu____11238,
                                                             uu____11239)
                                                     with
                                                     | ((x,uu____11249),
                                                        (b,uu____11251)) ->
                                                         let uu____11256 =
                                                           let uu____11261 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11261) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11256)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11263 =
                                            let uu____11274 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11274) in
                                          (uu____11263, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11309 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11309 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11361) ->
                              let uu____11366 =
                                let uu____11377 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____11377 in
                              (uu____11366, true)
                          | uu____11410 when Prims.op_Negation norm1 ->
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
                          | uu____11412 ->
                              let uu____11413 =
                                let uu____11414 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11415 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11414
                                  uu____11415 in
                              failwith uu____11413)
                     | uu____11428 ->
                         let uu____11429 =
                           let uu____11430 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11430.FStar_Syntax_Syntax.n in
                         (match uu____11429 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11457 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11457 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11475 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11475 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11523 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11551 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11551
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11558 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11599  ->
                            fun lb  ->
                              match uu____11599 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11650 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11650
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11653 =
                                      let uu____11661 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11661
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11653 with
                                    | (tok,decl,env2) ->
                                        let uu____11686 =
                                          let uu____11693 =
                                            let uu____11699 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11699, tok) in
                                          uu____11693 :: toks in
                                        (uu____11686, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11558 with
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
                        | uu____11801 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____11806 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11806 vars)
                            else
                              (let uu____11808 =
                                 let uu____11812 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11812) in
                               FStar_SMTEncoding_Util.mkApp uu____11808) in
                      let uu____11817 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_11819  ->
                                 match uu___116_11819 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11820 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11823 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11823))) in
                      if uu____11817
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11843;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11845;
                                FStar_Syntax_Syntax.lbeff = uu____11846;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11887 =
                                 let uu____11891 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11891 with
                                 | (tcenv',uu____11902,e_t) ->
                                     let uu____11906 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11913 -> failwith "Impossible" in
                                     (match uu____11906 with
                                      | (e1,t_norm1) ->
                                          ((let uu___150_11922 = env1 in
                                            {
                                              bindings =
                                                (uu___150_11922.bindings);
                                              depth = (uu___150_11922.depth);
                                              tcenv = tcenv';
                                              warn = (uu___150_11922.warn);
                                              cache = (uu___150_11922.cache);
                                              nolabels =
                                                (uu___150_11922.nolabels);
                                              use_zfuel_name =
                                                (uu___150_11922.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___150_11922.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___150_11922.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11887 with
                                | (env',e1,t_norm1) ->
                                    let uu____11929 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11929 with
                                     | ((binders,body,uu____11941,uu____11942),curry)
                                         ->
                                         ((let uu____11949 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11949
                                           then
                                             let uu____11950 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11951 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11950 uu____11951
                                           else ());
                                          (let uu____11953 =
                                             encode_binders
                                               FStar_Pervasives_Native.None
                                               binders env' in
                                           match uu____11953 with
                                           | (vars,guards,env'1,binder_decls,uu____11969)
                                               ->
                                               let body1 =
                                                 let uu____11977 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11977
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11980 =
                                                 let uu____11985 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11985
                                                 then
                                                   let uu____11991 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11992 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11991, uu____11992)
                                                 else
                                                   (let uu____11998 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11998)) in
                                               (match uu____11980 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12012 =
                                                        let uu____12016 =
                                                          let uu____12017 =
                                                            let uu____12023 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12023) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12017 in
                                                        let uu____12029 =
                                                          let uu____12031 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          FStar_Pervasives_Native.Some
                                                            uu____12031 in
                                                        (uu____12016,
                                                          uu____12029,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12012 in
                                                    let uu____12033 =
                                                      let uu____12035 =
                                                        let uu____12037 =
                                                          let uu____12039 =
                                                            let uu____12041 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12041 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12039 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12037 in
                                                      FStar_List.append
                                                        decls1 uu____12035 in
                                                    (uu____12033, env1))))))
                           | uu____12044 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12063 = varops.fresh "fuel" in
                             (uu____12063, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12066 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12105  ->
                                     fun uu____12106  ->
                                       match (uu____12105, uu____12106) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12188 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12188 in
                                           let gtok =
                                             let uu____12190 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12190 in
                                           let env3 =
                                             let uu____12192 =
                                               let uu____12194 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  ->
                                                    FStar_Pervasives_Native.Some
                                                      _0_36) uu____12194 in
                                             push_free_var env2 flid gtok
                                               uu____12192 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12066 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12280
                                 t_norm uu____12282 =
                                 match (uu____12280, uu____12282) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12309;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12310;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12327 =
                                       let uu____12331 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12331 with
                                       | (tcenv',uu____12346,e_t) ->
                                           let uu____12350 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12357 ->
                                                 failwith "Impossible" in
                                           (match uu____12350 with
                                            | (e1,t_norm1) ->
                                                ((let uu___151_12366 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___151_12366.bindings);
                                                    depth =
                                                      (uu___151_12366.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___151_12366.warn);
                                                    cache =
                                                      (uu___151_12366.cache);
                                                    nolabels =
                                                      (uu___151_12366.nolabels);
                                                    use_zfuel_name =
                                                      (uu___151_12366.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___151_12366.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___151_12366.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12327 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12376 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12376
                                            then
                                              let uu____12377 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12378 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12379 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12377 uu____12378
                                                uu____12379
                                            else ());
                                           (let uu____12381 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12381 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12403 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12403
                                                  then
                                                    let uu____12404 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12405 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12406 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12407 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12404 uu____12405
                                                      uu____12406 uu____12407
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12411 =
                                                    encode_binders
                                                      FStar_Pervasives_Native.None
                                                      binders env' in
                                                  match uu____12411 with
                                                  | (vars,guards,env'1,binder_decls,uu____12429)
                                                      ->
                                                      let decl_g =
                                                        let uu____12437 =
                                                          let uu____12443 =
                                                            let uu____12445 =
                                                              FStar_List.map
                                                                FStar_Pervasives_Native.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12445 in
                                                          (g, uu____12443,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (FStar_Pervasives_Native.Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12437 in
                                                      let env02 =
                                                        push_zfuel_name env01
                                                          flid g in
                                                      let decl_g_tok =
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          (gtok, [],
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (FStar_Pervasives_Native.Some
                                                               "Token for fuel-instrumented partial applications")) in
                                                      let vars_tm =
                                                        FStar_List.map
                                                          FStar_SMTEncoding_Util.mkFreeV
                                                          vars in
                                                      let app =
                                                        let uu____12460 =
                                                          let uu____12464 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12464) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12460 in
                                                      let gsapp =
                                                        let uu____12470 =
                                                          let uu____12474 =
                                                            let uu____12476 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12476 ::
                                                              vars_tm in
                                                          (g, uu____12474) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12470 in
                                                      let gmax =
                                                        let uu____12480 =
                                                          let uu____12484 =
                                                            let uu____12486 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12486 ::
                                                              vars_tm in
                                                          (g, uu____12484) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12480 in
                                                      let body1 =
                                                        let uu____12490 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12490
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12492 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12492 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12503
                                                               =
                                                               let uu____12507
                                                                 =
                                                                 let uu____12508
                                                                   =
                                                                   let uu____12516
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                   ([[gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12516) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12508 in
                                                               let uu____12527
                                                                 =
                                                                 let uu____12529
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____12529 in
                                                               (uu____12507,
                                                                 uu____12527,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12503 in
                                                           let eqn_f =
                                                             let uu____12532
                                                               =
                                                               let uu____12536
                                                                 =
                                                                 let uu____12537
                                                                   =
                                                                   let uu____12543
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12543) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12537 in
                                                               (uu____12536,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12532 in
                                                           let eqn_g' =
                                                             let uu____12551
                                                               =
                                                               let uu____12555
                                                                 =
                                                                 let uu____12556
                                                                   =
                                                                   let uu____12562
                                                                    =
                                                                    let uu____12563
                                                                    =
                                                                    let uu____12566
                                                                    =
                                                                    let uu____12567
                                                                    =
                                                                    let uu____12571
                                                                    =
                                                                    let uu____12573
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12573
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12571) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12567 in
                                                                    (gsapp,
                                                                    uu____12566) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12563 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12562) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12556 in
                                                               (uu____12555,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12551 in
                                                           let uu____12585 =
                                                             let uu____12590
                                                               =
                                                               encode_binders
                                                                 FStar_Pervasives_Native.None
                                                                 formals
                                                                 env02 in
                                                             match uu____12590
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12607)
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
                                                                    let uu____12622
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12622
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12625
                                                                    =
                                                                    let uu____12629
                                                                    =
                                                                    let uu____12630
                                                                    =
                                                                    let uu____12636
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12636) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12630 in
                                                                    (uu____12629,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12625 in
                                                                 let uu____12647
                                                                   =
                                                                   let uu____12651
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env3
                                                                    gapp in
                                                                   match uu____12651
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12659
                                                                    =
                                                                    let uu____12661
                                                                    =
                                                                    let uu____12662
                                                                    =
                                                                    let uu____12666
                                                                    =
                                                                    let uu____12667
                                                                    =
                                                                    let uu____12673
                                                                    =
                                                                    let uu____12674
                                                                    =
                                                                    let uu____12677
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12677,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12674 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12673) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12667 in
                                                                    (uu____12666,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12662 in
                                                                    [uu____12661] in
                                                                    (d3,
                                                                    uu____12659) in
                                                                 (match uu____12647
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12585
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
                               let uu____12712 =
                                 let uu____12719 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12755  ->
                                      fun uu____12756  ->
                                        match (uu____12755, uu____12756) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12842 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12842 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12719 in
                               (match uu____12712 with
                                | (decls2,eqns,env01) ->
                                    let uu____12882 =
                                      let isDeclFun uu___117_12890 =
                                        match uu___117_12890 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12891 -> true
                                        | uu____12897 -> false in
                                      let uu____12898 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12898
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12882 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12925 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12925
                     (FStar_String.concat " and ") in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg) in
                 ([decl], env))
let rec encode_sigelt:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12958 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____12958 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____12961 = encode_sigelt' env se in
      match uu____12961 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12971 =
                  let uu____12972 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____12972 in
                [uu____12971]
            | uu____12973 ->
                let uu____12974 =
                  let uu____12976 =
                    let uu____12977 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12977 in
                  uu____12976 :: g in
                let uu____12978 =
                  let uu____12980 =
                    let uu____12981 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12981 in
                  [uu____12980] in
                FStar_List.append uu____12974 uu____12978 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____12991 =
          let uu____12992 = FStar_Syntax_Subst.compress t in
          uu____12992.FStar_Syntax_Syntax.n in
        match uu____12991 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____12996)) -> s = "opaque_to_smt"
        | uu____12997 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13000 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13003 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13005 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13007 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13015 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13018 =
            let uu____13019 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13019 Prims.op_Negation in
          if uu____13018
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13039 ->
                   let uu____13040 =
                     let uu____13043 =
                       let uu____13044 =
                         let uu____13059 =
                           FStar_All.pipe_left
                             (fun _0_37  ->
                                FStar_Pervasives_Native.Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Parser_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13059) in
                       FStar_Syntax_Syntax.Tm_abs uu____13044 in
                     FStar_Syntax_Syntax.mk uu____13043 in
                   uu____13040 FStar_Pervasives_Native.None
                     tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13112 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13112 with
               | (aname,atok,env2) ->
                   let uu____13122 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13122 with
                    | (formals,uu____13132) ->
                        let uu____13139 =
                          let uu____13142 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13142 env2 in
                        (match uu____13139 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13150 =
                                 let uu____13151 =
                                   let uu____13157 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13165  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13157,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13151 in
                               [uu____13150;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____13172 =
                               let aux uu____13201 uu____13202 =
                                 match (uu____13201, uu____13202) with
                                 | ((bv,uu____13229),(env3,acc_sorts,acc)) ->
                                     let uu____13250 = gen_term_var env3 bv in
                                     (match uu____13250 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13172 with
                              | (uu____13288,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13302 =
                                      let uu____13306 =
                                        let uu____13307 =
                                          let uu____13313 =
                                            let uu____13314 =
                                              let uu____13317 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13317) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13314 in
                                          ([[app]], xs_sorts, uu____13313) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13307 in
                                      (uu____13306,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13302 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13329 =
                                      let uu____13333 =
                                        let uu____13334 =
                                          let uu____13340 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13340) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13334 in
                                      (uu____13333,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13329 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13350 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13350 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13366,uu____13367)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____13368 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13368 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13379,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13384 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13386  ->
                      match uu___118_13386 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13387 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13390 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13391 -> false)) in
            Prims.op_Negation uu____13384 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____13397 = encode_top_level_val env fv t quals in
             match uu____13397 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13409 =
                   let uu____13411 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13411 in
                 (uu____13409, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13416 = encode_formula f env in
          (match uu____13416 with
           | (f1,decls) ->
               let g =
                 let uu____13425 =
                   let uu____13426 =
                     let uu____13430 =
                       let uu____13432 =
                         let uu____13433 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13433 in
                       FStar_Pervasives_Native.Some uu____13432 in
                     let uu____13434 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13430, uu____13434) in
                   FStar_SMTEncoding_Util.mkAssume uu____13426 in
                 [uu____13425] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13438,attrs) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right attrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let uu____13446 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13453 =
                       let uu____13458 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13458.FStar_Syntax_Syntax.fv_name in
                     uu____13453.FStar_Syntax_Syntax.v in
                   let uu____13462 =
                     let uu____13463 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13463 in
                   if uu____13462
                   then
                     let val_decl =
                       let uu___152_13478 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___152_13478.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___152_13478.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13482 = encode_sigelt' env1 val_decl in
                     match uu____13482 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____13446 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13499,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13501;
                          FStar_Syntax_Syntax.lbtyp = uu____13502;
                          FStar_Syntax_Syntax.lbeff = uu____13503;
                          FStar_Syntax_Syntax.lbdef = uu____13504;_}::[]),uu____13505,uu____13506)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____13520 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13520 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13543 =
                   let uu____13545 =
                     let uu____13546 =
                       let uu____13550 =
                         let uu____13551 =
                           let uu____13557 =
                             let uu____13558 =
                               let uu____13561 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13561) in
                             FStar_SMTEncoding_Util.mkEq uu____13558 in
                           ([[b2t_x]], [xx], uu____13557) in
                         FStar_SMTEncoding_Util.mkForall uu____13551 in
                       (uu____13550,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13546 in
                   [uu____13545] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____13543 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13578,uu____13579,uu____13580)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_13586  ->
                  match uu___119_13586 with
                  | FStar_Syntax_Syntax.Discriminator uu____13587 -> true
                  | uu____13588 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13590,lids,uu____13592) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13599 =
                     let uu____13600 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13600.FStar_Ident.idText in
                   uu____13599 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_13602  ->
                     match uu___120_13602 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13603 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13606,uu____13607)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_13617  ->
                  match uu___121_13617 with
                  | FStar_Syntax_Syntax.Projector uu____13618 -> true
                  | uu____13621 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13628 = try_lookup_free_var env l in
          (match uu____13628 with
           | FStar_Pervasives_Native.Some uu____13632 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___153_13635 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___153_13635.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___153_13635.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13641,uu____13642) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13654) ->
          let uu____13659 = encode_sigelts env ses in
          (match uu____13659 with
           | (g,env1) ->
               let uu____13669 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_13679  ->
                         match uu___122_13679 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13680;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13681;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13682;_}
                             -> false
                         | uu____13684 -> true)) in
               (match uu____13669 with
                | (g',inversions) ->
                    let uu____13693 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_13703  ->
                              match uu___123_13703 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13704 ->
                                  true
                              | uu____13710 -> false)) in
                    (match uu____13693 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13721,tps,k,uu____13724,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_13734  ->
                    match uu___124_13734 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13735 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13742 = c in
              match uu____13742 with
              | (name,args,uu____13746,uu____13747,uu____13748) ->
                  let uu____13751 =
                    let uu____13752 =
                      let uu____13758 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13765  ->
                                match uu____13765 with
                                | (uu____13769,sort,uu____13771) -> sort)) in
                      (name, uu____13758, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13752 in
                  [uu____13751]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13789 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13792 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13792 FStar_Option.isNone)) in
            if uu____13789
            then []
            else
              (let uu____13809 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13809 with
               | (xxsym,xx) ->
                   let uu____13815 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13826  ->
                             fun l  ->
                               match uu____13826 with
                               | (out,decls) ->
                                   let uu____13838 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13838 with
                                    | (uu____13844,data_t) ->
                                        let uu____13846 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13846 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13875 =
                                                 let uu____13876 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13876.FStar_Syntax_Syntax.n in
                                               match uu____13875 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13884,indices) ->
                                                   indices
                                               | uu____13900 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13912  ->
                                                         match uu____13912
                                                         with
                                                         | (x,uu____13916) ->
                                                             let uu____13917
                                                               =
                                                               let uu____13918
                                                                 =
                                                                 let uu____13922
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13922,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13918 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13917)
                                                    env) in
                                             let uu____13924 =
                                               encode_args indices env1 in
                                             (match uu____13924 with
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
                                                      let uu____13944 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13952
                                                                 =
                                                                 let uu____13955
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13955,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13952)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13944
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13957 =
                                                      let uu____13958 =
                                                        let uu____13961 =
                                                          let uu____13962 =
                                                            let uu____13965 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13965,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13962 in
                                                        (out, uu____13961) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13958 in
                                                    (uu____13957,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13815 with
                    | (data_ax,decls) ->
                        let uu____13973 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13973 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13984 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13984 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13987 =
                                 let uu____13991 =
                                   let uu____13992 =
                                     let uu____13998 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14006 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13998,
                                       uu____14006) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13992 in
                                 let uu____14014 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13991,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____14014) in
                               FStar_SMTEncoding_Util.mkAssume uu____13987 in
                             let pattern_guarded_inversion =
                               let uu____14018 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14018
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14026 =
                                   let uu____14027 =
                                     let uu____14031 =
                                       let uu____14032 =
                                         let uu____14038 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14046 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14038, uu____14046) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14032 in
                                     let uu____14054 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14031,
                                       (FStar_Pervasives_Native.Some
                                          "inversion axiom"), uu____14054) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14027 in
                                 [uu____14026]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14057 =
            let uu____14065 =
              let uu____14066 = FStar_Syntax_Subst.compress k in
              uu____14066.FStar_Syntax_Syntax.n in
            match uu____14065 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14095 -> (tps, k) in
          (match uu____14057 with
           | (formals,res) ->
               let uu____14110 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14110 with
                | (formals1,res1) ->
                    let uu____14117 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____14117 with
                     | (vars,guards,env',binder_decls,uu____14132) ->
                         let uu____14139 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14139 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14152 =
                                  let uu____14156 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14156) in
                                FStar_SMTEncoding_Util.mkApp uu____14152 in
                              let uu____14161 =
                                let tname_decl =
                                  let uu____14167 =
                                    let uu____14168 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14183  ->
                                              match uu____14183 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14191 = varops.next_id () in
                                    (tname, uu____14168,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14191, false) in
                                  constructor_or_logic_type_decl uu____14167 in
                                let uu____14196 =
                                  match vars with
                                  | [] ->
                                      let uu____14203 =
                                        let uu____14204 =
                                          let uu____14206 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_38) uu____14206 in
                                        push_free_var env1 t tname
                                          uu____14204 in
                                      ([], uu____14203)
                                  | uu____14210 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____14216 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14216 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14225 =
                                          let uu____14229 =
                                            let uu____14230 =
                                              let uu____14238 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____14238) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14230 in
                                          (uu____14229,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14225 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14196 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14161 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14261 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____14261 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14275 =
                                               let uu____14276 =
                                                 let uu____14280 =
                                                   let uu____14281 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14281 in
                                                 (uu____14280,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14276 in
                                             [uu____14275]
                                           else [] in
                                         let uu____14284 =
                                           let uu____14286 =
                                             let uu____14288 =
                                               let uu____14289 =
                                                 let uu____14293 =
                                                   let uu____14294 =
                                                     let uu____14300 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14300) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14294 in
                                                 (uu____14293,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14289 in
                                             [uu____14288] in
                                           FStar_List.append karr uu____14286 in
                                         FStar_List.append decls1 uu____14284 in
                                   let aux =
                                     let uu____14309 =
                                       let uu____14311 =
                                         inversion_axioms tapp vars in
                                       let uu____14313 =
                                         let uu____14315 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14315] in
                                       FStar_List.append uu____14311
                                         uu____14313 in
                                     FStar_List.append kindingAx uu____14309 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14320,uu____14321,uu____14322,uu____14323,uu____14324)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14329,t,uu____14331,n_tps,uu____14333) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14338 = new_term_constant_and_tok_from_lid env d in
          (match uu____14338 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14349 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14349 with
                | (formals,t_res) ->
                    let uu____14371 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14371 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14380 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____14380 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14418 =
                                            mk_term_projector_name d x in
                                          (uu____14418,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14420 =
                                  let uu____14430 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14430, true) in
                                FStar_All.pipe_right uu____14420
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
                              let uu____14452 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____14452 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14460::uu____14461 ->
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
                                         let uu____14486 =
                                           let uu____14492 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14492) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14486
                                     | uu____14505 -> tok_typing in
                                   let uu____14510 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____14510 with
                                    | (vars',guards',env'',decls_formals,uu____14525)
                                        ->
                                        let uu____14532 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred
                                            (FStar_Pervasives_Native.Some
                                               fuel_tm) t_res env'' dapp1 in
                                        (match uu____14532 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14551 ->
                                                   let uu____14555 =
                                                     let uu____14556 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14556 in
                                                   [uu____14555] in
                                             let encode_elim uu____14563 =
                                               let uu____14564 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14564 with
                                               | (head1,args) ->
                                                   let uu____14593 =
                                                     let uu____14594 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14594.FStar_Syntax_Syntax.n in
                                                   (match uu____14593 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____14601;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14602;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14603;_},uu____14604)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14614 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14614
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               orig_arg arg
                                                               xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____14643
                                                                    ->
                                                                    let uu____14644
                                                                    =
                                                                    let uu____14645
                                                                    =
                                                                    let uu____14648
                                                                    =
                                                                    let uu____14649
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14649 in
                                                                    (uu____14648,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____14645 in
                                                                    raise
                                                                    uu____14644 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14657
                                                                    =
                                                                    let uu____14658
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14658 in
                                                                    if
                                                                    uu____14657
                                                                    then
                                                                    let uu____14665
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14665]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14667
                                                               =
                                                               let uu____14674
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14694
                                                                     ->
                                                                    fun
                                                                    uu____14695
                                                                     ->
                                                                    match 
                                                                    (uu____14694,
                                                                    uu____14695)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____14746
                                                                    =
                                                                    let uu____14750
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14750 in
                                                                    (match uu____14746
                                                                    with
                                                                    | 
                                                                    (uu____14757,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14763
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____14763
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14765
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14765
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
                                                                 uu____14674 in
                                                             (match uu____14667
                                                              with
                                                              | (uu____14773,arg_vars,elim_eqns_or_guards,uu____14776)
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
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____14795
                                                                    =
                                                                    let uu____14799
                                                                    =
                                                                    let uu____14800
                                                                    =
                                                                    let uu____14806
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14812
                                                                    =
                                                                    let uu____14813
                                                                    =
                                                                    let uu____14816
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14816) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14813 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14806,
                                                                    uu____14812) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14800 in
                                                                    (uu____14799,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14795 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14829
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14829,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14831
                                                                    =
                                                                    let uu____14835
                                                                    =
                                                                    let uu____14836
                                                                    =
                                                                    let uu____14842
                                                                    =
                                                                    let uu____14845
                                                                    =
                                                                    let uu____14847
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14847] in
                                                                    [uu____14845] in
                                                                    let uu____14850
                                                                    =
                                                                    let uu____14851
                                                                    =
                                                                    let uu____14854
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14855
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14854,
                                                                    uu____14855) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14851 in
                                                                    (uu____14842,
                                                                    [x],
                                                                    uu____14850) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14836 in
                                                                    let uu____14865
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14835,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____14865) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14831
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14870
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
                                                                    (let uu____14885
                                                                    =
                                                                    let uu____14886
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14886
                                                                    dapp1 in
                                                                    [uu____14885]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14870
                                                                    FStar_List.flatten in
                                                                    let uu____14890
                                                                    =
                                                                    let uu____14894
                                                                    =
                                                                    let uu____14895
                                                                    =
                                                                    let uu____14901
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14907
                                                                    =
                                                                    let uu____14908
                                                                    =
                                                                    let uu____14911
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14911) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14908 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14901,
                                                                    uu____14907) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14895 in
                                                                    (uu____14894,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14890) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14927 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14927
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               orig_arg arg
                                                               xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____14956
                                                                    ->
                                                                    let uu____14957
                                                                    =
                                                                    let uu____14958
                                                                    =
                                                                    let uu____14961
                                                                    =
                                                                    let uu____14962
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14962 in
                                                                    (uu____14961,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____14958 in
                                                                    raise
                                                                    uu____14957 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14970
                                                                    =
                                                                    let uu____14971
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14971 in
                                                                    if
                                                                    uu____14970
                                                                    then
                                                                    let uu____14978
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14978]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14980
                                                               =
                                                               let uu____14987
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15007
                                                                     ->
                                                                    fun
                                                                    uu____15008
                                                                     ->
                                                                    match 
                                                                    (uu____15007,
                                                                    uu____15008)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15059
                                                                    =
                                                                    let uu____15063
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15063 in
                                                                    (match uu____15059
                                                                    with
                                                                    | 
                                                                    (uu____15070,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15076
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____15076
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15078
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15078
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
                                                                 uu____14987 in
                                                             (match uu____14980
                                                              with
                                                              | (uu____15086,arg_vars,elim_eqns_or_guards,uu____15089)
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
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____15108
                                                                    =
                                                                    let uu____15112
                                                                    =
                                                                    let uu____15113
                                                                    =
                                                                    let uu____15119
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15125
                                                                    =
                                                                    let uu____15126
                                                                    =
                                                                    let uu____15129
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15129) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15126 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15119,
                                                                    uu____15125) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15113 in
                                                                    (uu____15112,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15108 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15142
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15142,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15144
                                                                    =
                                                                    let uu____15148
                                                                    =
                                                                    let uu____15149
                                                                    =
                                                                    let uu____15155
                                                                    =
                                                                    let uu____15158
                                                                    =
                                                                    let uu____15160
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15160] in
                                                                    [uu____15158] in
                                                                    let uu____15163
                                                                    =
                                                                    let uu____15164
                                                                    =
                                                                    let uu____15167
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15168
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15167,
                                                                    uu____15168) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15164 in
                                                                    (uu____15155,
                                                                    [x],
                                                                    uu____15163) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15149 in
                                                                    let uu____15178
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15148,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15178) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15144
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15183
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
                                                                    (let uu____15198
                                                                    =
                                                                    let uu____15199
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15199
                                                                    dapp1 in
                                                                    [uu____15198]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15183
                                                                    FStar_List.flatten in
                                                                    let uu____15203
                                                                    =
                                                                    let uu____15207
                                                                    =
                                                                    let uu____15208
                                                                    =
                                                                    let uu____15214
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15220
                                                                    =
                                                                    let uu____15221
                                                                    =
                                                                    let uu____15224
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15224) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15221 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15214,
                                                                    uu____15220) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15208 in
                                                                    (uu____15207,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15203) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15234 ->
                                                        ((let uu____15236 =
                                                            let uu____15237 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15238 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15237
                                                              uu____15238 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15236);
                                                         ([], []))) in
                                             let uu____15241 = encode_elim () in
                                             (match uu____15241 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15253 =
                                                      let uu____15255 =
                                                        let uu____15257 =
                                                          let uu____15259 =
                                                            let uu____15261 =
                                                              let uu____15262
                                                                =
                                                                let uu____15268
                                                                  =
                                                                  let uu____15270
                                                                    =
                                                                    let uu____15271
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15271 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____15270 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15268) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15262 in
                                                            [uu____15261] in
                                                          let uu____15274 =
                                                            let uu____15276 =
                                                              let uu____15278
                                                                =
                                                                let uu____15280
                                                                  =
                                                                  let uu____15282
                                                                    =
                                                                    let uu____15284
                                                                    =
                                                                    let uu____15286
                                                                    =
                                                                    let uu____15287
                                                                    =
                                                                    let uu____15291
                                                                    =
                                                                    let uu____15292
                                                                    =
                                                                    let uu____15298
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15298) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15292 in
                                                                    (uu____15291,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15287 in
                                                                    let uu____15305
                                                                    =
                                                                    let uu____15307
                                                                    =
                                                                    let uu____15308
                                                                    =
                                                                    let uu____15312
                                                                    =
                                                                    let uu____15313
                                                                    =
                                                                    let uu____15319
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____15325
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15319,
                                                                    uu____15325) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15313 in
                                                                    (uu____15312,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15308 in
                                                                    [uu____15307] in
                                                                    uu____15286
                                                                    ::
                                                                    uu____15305 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15284 in
                                                                  FStar_List.append
                                                                    uu____15282
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15280 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15278 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15276 in
                                                          FStar_List.append
                                                            uu____15259
                                                            uu____15274 in
                                                        FStar_List.append
                                                          decls3 uu____15257 in
                                                      FStar_List.append
                                                        decls2 uu____15255 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15253 in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))
and encode_sigelts:
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____15346  ->
              fun se  ->
                match uu____15346 with
                | (g,env1) ->
                    let uu____15358 = encode_sigelt env1 se in
                    (match uu____15358 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15394 =
        match uu____15394 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15412 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____15417 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15417
                   then
                     let uu____15418 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15419 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15420 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15418 uu____15419 uu____15420
                   else ());
                  (let uu____15422 = encode_term t1 env1 in
                   match uu____15422 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15432 =
                         let uu____15436 =
                           let uu____15437 =
                             let uu____15438 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15438
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15437 in
                         new_term_constant_from_string env1 x uu____15436 in
                       (match uu____15432 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____15449 = FStar_Options.log_queries () in
                              if uu____15449
                              then
                                let uu____15451 =
                                  let uu____15452 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15453 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15454 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15452 uu____15453 uu____15454 in
                                FStar_Pervasives_Native.Some uu____15451
                              else FStar_Pervasives_Native.None in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name) in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax]) in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15465,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____15474 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15474 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15487,se,uu____15489) ->
                 let uu____15492 = encode_sigelt env1 se in
                 (match uu____15492 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15502,se) ->
                 let uu____15506 = encode_sigelt env1 se in
                 (match uu____15506 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15516 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15516 with | (uu____15528,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15573  ->
            match uu____15573 with
            | (l,uu____15580,uu____15581) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((FStar_Pervasives_Native.fst l), [],
                    FStar_SMTEncoding_Term.Bool_sort,
                    FStar_Pervasives_Native.None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15602  ->
            match uu____15602 with
            | (l,uu____15610,uu____15611) ->
                let uu____15616 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (FStar_Pervasives_Native.fst l) in
                let uu____15617 =
                  let uu____15619 =
                    let uu____15620 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15620 in
                  [uu____15619] in
                uu____15616 :: uu____15617)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15631 =
      let uu____15633 =
        let uu____15634 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15636 =
          let uu____15637 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15637 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15634;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15636
        } in
      [uu____15633] in
    FStar_ST.write last_env uu____15631
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15647 = FStar_ST.read last_env in
      match uu____15647 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15653 ->
          let uu___154_15655 = e in
          let uu____15656 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___154_15655.bindings);
            depth = (uu___154_15655.depth);
            tcenv;
            warn = (uu___154_15655.warn);
            cache = (uu___154_15655.cache);
            nolabels = (uu___154_15655.nolabels);
            use_zfuel_name = (uu___154_15655.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15655.encode_non_total_function_typ);
            current_module_name = uu____15656
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15660 = FStar_ST.read last_env in
    match uu____15660 with
    | [] -> failwith "Empty env stack"
    | uu____15665::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15673  ->
    let uu____15674 = FStar_ST.read last_env in
    match uu____15674 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___155_15685 = hd1 in
          {
            bindings = (uu___155_15685.bindings);
            depth = (uu___155_15685.depth);
            tcenv = (uu___155_15685.tcenv);
            warn = (uu___155_15685.warn);
            cache = refs;
            nolabels = (uu___155_15685.nolabels);
            use_zfuel_name = (uu___155_15685.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_15685.encode_non_total_function_typ);
            current_module_name = (uu___155_15685.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15691  ->
    let uu____15692 = FStar_ST.read last_env in
    match uu____15692 with
    | [] -> failwith "Popping an empty stack"
    | uu____15697::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15705  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15708  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15711  ->
    let uu____15712 = FStar_ST.read last_env in
    match uu____15712 with
    | hd1::uu____15718::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15724 -> failwith "Impossible"
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
        | (uu____15773::uu____15774,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___156_15778 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___156_15778.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___156_15778.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___156_15778.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15779 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15790 =
        let uu____15792 =
          let uu____15793 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15793 in
        let uu____15794 = open_fact_db_tags env in uu____15792 :: uu____15794 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15790
let encode_top_level_facts:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env)) in
      let uu____15809 = encode_sigelt env se in
      match uu____15809 with
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
        let uu____15834 = FStar_Options.log_queries () in
        if uu____15834
        then
          let uu____15836 =
            let uu____15837 =
              let uu____15838 =
                let uu____15839 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15839 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15838 in
            FStar_SMTEncoding_Term.Caption uu____15837 in
          uu____15836 :: decls
        else decls in
      let env =
        let uu____15846 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15846 tcenv in
      let uu____15847 = encode_top_level_facts env se in
      match uu____15847 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15856 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15856))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15867 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15867
       then
         let uu____15868 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15868
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15889  ->
                 fun se  ->
                   match uu____15889 with
                   | (g,env2) ->
                       let uu____15901 = encode_top_level_facts env2 se in
                       (match uu____15901 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15914 =
         encode_signature
           (let uu___157_15918 = env in
            {
              bindings = (uu___157_15918.bindings);
              depth = (uu___157_15918.depth);
              tcenv = (uu___157_15918.tcenv);
              warn = false;
              cache = (uu___157_15918.cache);
              nolabels = (uu___157_15918.nolabels);
              use_zfuel_name = (uu___157_15918.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___157_15918.encode_non_total_function_typ);
              current_module_name = (uu___157_15918.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15914 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15930 = FStar_Options.log_queries () in
             if uu____15930
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___158_15935 = env1 in
               {
                 bindings = (uu___158_15935.bindings);
                 depth = (uu___158_15935.depth);
                 tcenv = (uu___158_15935.tcenv);
                 warn = true;
                 cache = (uu___158_15935.cache);
                 nolabels = (uu___158_15935.nolabels);
                 use_zfuel_name = (uu___158_15935.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___158_15935.encode_non_total_function_typ);
                 current_module_name = (uu___158_15935.current_module_name)
               });
            (let uu____15937 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15937
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls1)))
let encode_query:
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_ErrorReporting.label
                                                  Prims.list,FStar_SMTEncoding_Term.decl,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple4
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____15972 =
           let uu____15973 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15973.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15972);
        (let env =
           let uu____15975 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15975 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15982 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16003 = aux rest in
                 (match uu____16003 with
                  | (out,rest1) ->
                      let t =
                        let uu____16021 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____16021 with
                        | FStar_Pervasives_Native.Some uu____16025 ->
                            let uu____16026 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16026
                              x.FStar_Syntax_Syntax.sort
                        | uu____16027 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____16030 =
                        let uu____16032 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___159_16033 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___159_16033.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___159_16033.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16032 :: out in
                      (uu____16030, rest1))
             | uu____16036 -> ([], bindings1) in
           let uu____16040 = aux bindings in
           match uu____16040 with
           | (closing,bindings1) ->
               let uu____16054 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16054, bindings1) in
         match uu____15982 with
         | (q1,bindings1) ->
             let uu____16067 =
               let uu____16070 =
                 FStar_List.filter
                   (fun uu___125_16072  ->
                      match uu___125_16072 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16073 ->
                          false
                      | uu____16077 -> true) bindings1 in
               encode_env_bindings env uu____16070 in
             (match uu____16067 with
              | (env_decls,env1) ->
                  ((let uu____16088 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16088
                    then
                      let uu____16089 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16089
                    else ());
                   (let uu____16091 = encode_formula q1 env1 in
                    match uu____16091 with
                    | (phi,qdecls) ->
                        let uu____16103 =
                          let uu____16106 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16106 phi in
                        (match uu____16103 with
                         | (labels,phi1) ->
                             let uu____16116 = encode_labels labels in
                             (match uu____16116 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____16137 =
                                      let uu____16141 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16142 =
                                        varops.mk_unique "@query" in
                                      (uu____16141,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____16142) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16137 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16155 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16155 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16157 = encode_formula q env in
       match uu____16157 with
       | (f,uu____16161) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16163) -> true
             | uu____16166 -> false)))