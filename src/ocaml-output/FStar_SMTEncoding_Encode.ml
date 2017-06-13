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
  let new_scope uu____435 =
    let uu____436 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____438 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____436, uu____438) in
  let scopes =
    let uu____449 = let uu____455 = new_scope () in [uu____455] in
    FStar_Util.mk_ref uu____449 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____480 =
        let uu____482 = FStar_ST.read scopes in
        FStar_Util.find_map uu____482
          (fun uu____499  ->
             match uu____499 with
             | (names1,uu____506) -> FStar_Util.smap_try_find names1 y1) in
      match uu____480 with
      | None  -> y1
      | Some uu____511 ->
          (FStar_Util.incr ctr;
           (let uu____516 =
              let uu____517 =
                let uu____518 = FStar_ST.read ctr in
                Prims.string_of_int uu____518 in
              Prims.strcat "__" uu____517 in
            Prims.strcat y1 uu____516)) in
    let top_scope =
      let uu____523 =
        let uu____528 = FStar_ST.read scopes in FStar_List.hd uu____528 in
      FStar_All.pipe_left FStar_Pervasives.fst uu____523 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____567 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____578 =
      let uu____579 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____579 in
    FStar_Util.format2 "%s_%s" pfx uu____578 in
  let string_const s =
    let uu____584 =
      let uu____586 = FStar_ST.read scopes in
      FStar_Util.find_map uu____586
        (fun uu____603  ->
           match uu____603 with
           | (uu____609,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____584 with
    | Some f -> f
    | None  ->
        let id = next_id1 () in
        let f =
          let uu____618 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____618 in
        let top_scope =
          let uu____621 =
            let uu____626 = FStar_ST.read scopes in FStar_List.hd uu____626 in
          FStar_All.pipe_left FStar_Pervasives.snd uu____621 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____654 =
    let uu____655 =
      let uu____661 = new_scope () in
      let uu____666 = FStar_ST.read scopes in uu____661 :: uu____666 in
    FStar_ST.write scopes uu____655 in
  let pop1 uu____693 =
    let uu____694 =
      let uu____700 = FStar_ST.read scopes in FStar_List.tl uu____700 in
    FStar_ST.write scopes uu____694 in
  let mark1 uu____727 = push1 () in
  let reset_mark1 uu____731 = pop1 () in
  let commit_mark1 uu____735 =
    let uu____736 = FStar_ST.read scopes in
    match uu____736 with
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
    | uu____796 -> failwith "Impossible" in
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
    let uu___126_805 = x in
    let uu____806 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____806;
      FStar_Syntax_Syntax.index = (uu___126_805.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___126_805.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term option* FStar_SMTEncoding_Term.term option)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____829 -> false
let __proj__Binding_var__item___0:
  binding -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____853 -> false
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
         (fun uu___102_1041  ->
            match uu___102_1041 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1044 -> [])) in
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
    let uu____1052 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___103_1056  ->
              match uu___103_1056 with
              | Binding_var (x,uu____1058) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1060,uu____1061,uu____1062) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1052 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string option =
  fun env  ->
    fun t  ->
      let uu____1095 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1095
      then
        let uu____1097 = FStar_Syntax_Print.term_to_string t in
        Some uu____1097
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1108 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1108)
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
        (let uu___127_1120 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___127_1120.tcenv);
           warn = (uu___127_1120.warn);
           cache = (uu___127_1120.cache);
           nolabels = (uu___127_1120.nolabels);
           use_zfuel_name = (uu___127_1120.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___127_1120.encode_non_total_function_typ);
           current_module_name = (uu___127_1120.current_module_name)
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
        (let uu___128_1133 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___128_1133.depth);
           tcenv = (uu___128_1133.tcenv);
           warn = (uu___128_1133.warn);
           cache = (uu___128_1133.cache);
           nolabels = (uu___128_1133.nolabels);
           use_zfuel_name = (uu___128_1133.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_1133.encode_non_total_function_typ);
           current_module_name = (uu___128_1133.current_module_name)
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
          (let uu___129_1149 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___129_1149.depth);
             tcenv = (uu___129_1149.tcenv);
             warn = (uu___129_1149.warn);
             cache = (uu___129_1149.cache);
             nolabels = (uu___129_1149.nolabels);
             use_zfuel_name = (uu___129_1149.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___129_1149.encode_non_total_function_typ);
             current_module_name = (uu___129_1149.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___130_1159 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___130_1159.depth);
          tcenv = (uu___130_1159.tcenv);
          warn = (uu___130_1159.warn);
          cache = (uu___130_1159.cache);
          nolabels = (uu___130_1159.nolabels);
          use_zfuel_name = (uu___130_1159.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___130_1159.encode_non_total_function_typ);
          current_module_name = (uu___130_1159.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___104_1175  ->
             match uu___104_1175 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1183 -> None) in
      let uu____1186 = aux a in
      match uu____1186 with
      | None  ->
          let a2 = unmangle a in
          let uu____1193 = aux a2 in
          (match uu____1193 with
           | None  ->
               let uu____1199 =
                 let uu____1200 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1201 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1200 uu____1201 in
               failwith uu____1199
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1221 =
        let uu___131_1222 = env in
        let uu____1223 =
          let uu____1225 =
            let uu____1226 =
              let uu____1233 =
                let uu____1235 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_39  -> Some _0_39) uu____1235 in
              (x, fname, uu____1233, None) in
            Binding_fvar uu____1226 in
          uu____1225 :: (env.bindings) in
        {
          bindings = uu____1223;
          depth = (uu___131_1222.depth);
          tcenv = (uu___131_1222.tcenv);
          warn = (uu___131_1222.warn);
          cache = (uu___131_1222.cache);
          nolabels = (uu___131_1222.nolabels);
          use_zfuel_name = (uu___131_1222.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_1222.encode_non_total_function_typ);
          current_module_name = (uu___131_1222.current_module_name)
        } in
      (fname, ftok, uu____1221)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option) option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___105_1257  ->
           match uu___105_1257 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1279 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1291 =
        lookup_binding env
          (fun uu___106_1293  ->
             match uu___106_1293 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1303 -> None) in
      FStar_All.pipe_right uu____1291 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option)
  =
  fun env  ->
    fun a  ->
      let uu____1316 = try_lookup_lid env a in
      match uu____1316 with
      | None  ->
          let uu____1333 =
            let uu____1334 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1334 in
          failwith uu____1333
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
          let uu___132_1365 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___132_1365.depth);
            tcenv = (uu___132_1365.tcenv);
            warn = (uu___132_1365.warn);
            cache = (uu___132_1365.cache);
            nolabels = (uu___132_1365.nolabels);
            use_zfuel_name = (uu___132_1365.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___132_1365.encode_non_total_function_typ);
            current_module_name = (uu___132_1365.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1377 = lookup_lid env x in
        match uu____1377 with
        | (t1,t2,uu____1385) ->
            let t3 =
              let uu____1391 =
                let uu____1395 =
                  let uu____1397 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1397] in
                (f, uu____1395) in
              FStar_SMTEncoding_Util.mkApp uu____1391 in
            let uu___133_1400 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___133_1400.depth);
              tcenv = (uu___133_1400.tcenv);
              warn = (uu___133_1400.warn);
              cache = (uu___133_1400.cache);
              nolabels = (uu___133_1400.nolabels);
              use_zfuel_name = (uu___133_1400.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___133_1400.encode_non_total_function_typ);
              current_module_name = (uu___133_1400.current_module_name)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term option =
  fun env  ->
    fun l  ->
      let uu____1410 = try_lookup_lid env l in
      match uu____1410 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1437 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1442,fuel::[]) ->
                         let uu____1445 =
                           let uu____1446 =
                             let uu____1447 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1447
                               FStar_Pervasives.fst in
                           FStar_Util.starts_with uu____1446 "fuel" in
                         if uu____1445
                         then
                           let uu____1449 =
                             let uu____1450 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1450
                               fuel in
                           FStar_All.pipe_left (fun _0_40  -> Some _0_40)
                             uu____1449
                         else Some t
                     | uu____1453 -> Some t)
                | uu____1454 -> None))
let lookup_free_var env a =
  let uu____1472 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1472 with
  | Some t -> t
  | None  ->
      let uu____1475 =
        let uu____1476 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1476 in
      failwith uu____1475
let lookup_free_var_name env a =
  let uu____1493 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1493 with | (x,uu____1500,uu____1501) -> x
let lookup_free_var_sym env a =
  let uu____1525 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1525 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1546;
             FStar_SMTEncoding_Term.rng = uu____1547;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1555 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1569 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name: env_t -> Prims.string -> FStar_SMTEncoding_Term.term option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___107_1578  ->
           match uu___107_1578 with
           | Binding_fvar (uu____1580,nm',tok,uu____1583) when nm = nm' ->
               tok
           | uu____1588 -> None)
let mkForall_fuel' n1 uu____1605 =
  match uu____1605 with
  | (pats,vars,body) ->
      let fallback uu____1621 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1624 = FStar_Options.unthrottle_inductives () in
      if uu____1624
      then fallback ()
      else
        (let uu____1626 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1626 with
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
                       | uu____1645 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1659 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1659
                     | uu____1661 ->
                         let uu____1662 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1662 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1665 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____1691 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____1699 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____1704 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____1705 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____1714 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____1729 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1731 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1731 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____1745;
             FStar_Syntax_Syntax.pos = uu____1746;
             FStar_Syntax_Syntax.vars = uu____1747;_},uu____1748)
          ->
          let uu____1763 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1763 FStar_Option.isNone
      | uu____1776 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1783 =
        let uu____1784 = FStar_Syntax_Util.un_uinst t in
        uu____1784.FStar_Syntax_Syntax.n in
      match uu____1783 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1787,uu____1788,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___108_1817  ->
                  match uu___108_1817 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1818 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1819,uu____1820,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1847 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1847 FStar_Option.isSome
      | uu____1860 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1867 = head_normal env t in
      if uu____1867
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
    let uu____1878 =
      let uu____1879 = FStar_Syntax_Syntax.null_binder t in [uu____1879] in
    let uu____1880 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1878 uu____1880 None
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
                    let uu____1907 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1907
                | s ->
                    let uu____1910 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1910) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___109_1922  ->
    match uu___109_1922 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1923 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____1951;
                       FStar_SMTEncoding_Term.rng = uu____1952;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1966) ->
              let uu____1971 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1985 -> false) args (FStar_List.rev xs)) in
              if uu____1971 then tok_of_name env f else None
          | (uu____1988,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1991 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1993 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1993)) in
              if uu____1991 then Some t else None
          | uu____1996 -> None in
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
    | uu____2087 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___110_2090  ->
    match uu___110_2090 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2092 =
          let uu____2096 =
            let uu____2098 =
              let uu____2099 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2099 in
            [uu____2098] in
          ("FStar.Char.Char", uu____2096) in
        FStar_SMTEncoding_Util.mkApp uu____2092
    | FStar_Const.Const_int (i,None ) ->
        let uu____2107 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2107
    | FStar_Const.Const_int (i,Some uu____2109) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2118) ->
        let uu____2121 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2121
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2125 =
          let uu____2126 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2126 in
        failwith uu____2125
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2145 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2153 ->
            let uu____2158 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2158
        | uu____2159 ->
            if norm1
            then let uu____2160 = whnf env t1 in aux false uu____2160
            else
              (let uu____2162 =
                 let uu____2163 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2164 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2163 uu____2164 in
               failwith uu____2162) in
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
    | uu____2185 ->
        let uu____2186 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2186)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2214::uu____2215::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Syntax_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2218::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2220 -> false
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
        (let uu____2358 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2358
         then
           let uu____2359 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2359
         else ());
        (let uu____2361 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2397  ->
                   fun b  ->
                     match uu____2397 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2440 =
                           let x = unmangle (fst b) in
                           let uu____2449 = gen_term_var env1 x in
                           match uu____2449 with
                           | (xxsym,xx,env') ->
                               let uu____2463 =
                                 let uu____2466 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2466 env1 xx in
                               (match uu____2463 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2440 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2361 with
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
          let uu____2554 = encode_term t env in
          match uu____2554 with
          | (t1,decls) ->
              let uu____2561 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2561, decls)
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
          let uu____2569 = encode_term t env in
          match uu____2569 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2578 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2578, decls)
               | Some f ->
                   let uu____2580 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2580, decls))
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
        let uu____2586 = encode_args args_e env in
        match uu____2586 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2598 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____2605 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____2605 in
            let binary arg_tms1 =
              let uu____2614 =
                let uu____2615 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____2615 in
              let uu____2616 =
                let uu____2617 =
                  let uu____2618 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2618 in
                FStar_SMTEncoding_Term.unboxInt uu____2617 in
              (uu____2614, uu____2616) in
            let mk_default uu____2623 =
              let uu____2624 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2624 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____2669 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2669
              then
                let uu____2670 = let uu____2671 = mk_args ts in op uu____2671 in
                FStar_All.pipe_right uu____2670 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____2694 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____2694
              then
                let uu____2695 = binary ts in
                match uu____2695 with
                | (t1,t2) ->
                    let uu____2700 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____2700
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2703 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____2703
                 then
                   let uu____2704 = op (binary ts) in
                   FStar_All.pipe_right uu____2704
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
            let uu____2794 =
              let uu____2800 =
                FStar_List.tryFind
                  (fun uu____2812  ->
                     match uu____2812 with
                     | (l,uu____2819) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____2800 FStar_Util.must in
            (match uu____2794 with
             | (uu____2844,op) ->
                 let uu____2852 = op arg_tms in (uu____2852, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2859 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2859
       then
         let uu____2860 = FStar_Syntax_Print.tag_of_term t in
         let uu____2861 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2862 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2860 uu____2861
           uu____2862
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2866 ->
           let uu____2887 =
             let uu____2888 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2889 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2890 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2891 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2888
               uu____2889 uu____2890 uu____2891 in
           failwith uu____2887
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2894 =
             let uu____2895 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2896 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2897 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2898 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2895
               uu____2896 uu____2897 uu____2898 in
           failwith uu____2894
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2902 =
             let uu____2903 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2903 in
           failwith uu____2902
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2908) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2938) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2947 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2947, [])
       | FStar_Syntax_Syntax.Tm_type uu____2953 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2956) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2962 = encode_const c in (uu____2962, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2977 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2977 with
            | (binders1,res) ->
                let uu____2984 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2984
                then
                  let uu____2987 = encode_binders None binders1 env in
                  (match uu____2987 with
                   | (vars,guards,env',decls,uu____3002) ->
                       let fsym =
                         let uu____3012 = varops.fresh "f" in
                         (uu____3012, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____3015 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___134_3019 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___134_3019.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___134_3019.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___134_3019.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___134_3019.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___134_3019.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___134_3019.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___134_3019.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___134_3019.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___134_3019.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___134_3019.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___134_3019.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___134_3019.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___134_3019.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___134_3019.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___134_3019.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___134_3019.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___134_3019.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___134_3019.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___134_3019.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___134_3019.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___134_3019.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___134_3019.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___134_3019.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___134_3019.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___134_3019.FStar_TypeChecker_Env.synth)
                            }) res in
                       (match uu____3015 with
                        | (pre_opt,res_t) ->
                            let uu____3026 =
                              encode_term_pred None res_t env' app in
                            (match uu____3026 with
                             | (res_pred,decls') ->
                                 let uu____3033 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____3040 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____3040, [])
                                   | Some pre ->
                                       let uu____3043 =
                                         encode_formula pre env' in
                                       (match uu____3043 with
                                        | (guard,decls0) ->
                                            let uu____3051 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3051, decls0)) in
                                 (match uu____3033 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3059 =
                                          let uu____3065 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3065) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3059 in
                                      let cvars =
                                        let uu____3075 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3075
                                          (FStar_List.filter
                                             (fun uu____3081  ->
                                                match uu____3081 with
                                                | (x,uu____3085) ->
                                                    x <> (fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3096 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3096 with
                                       | Some cache_entry ->
                                           let uu____3101 =
                                             let uu____3102 =
                                               let uu____3106 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3106) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3102 in
                                           (uu____3101,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____3117 =
                                               let uu____3118 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3118 in
                                             varops.mk_unique uu____3117 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars in
                                           let caption =
                                             let uu____3125 =
                                               FStar_Options.log_queries () in
                                             if uu____3125
                                             then
                                               let uu____3127 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____3127
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3133 =
                                               let uu____3137 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3137) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3133 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3145 =
                                               let uu____3149 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3149, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3145 in
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
                                             let uu____3162 =
                                               let uu____3166 =
                                                 let uu____3167 =
                                                   let uu____3173 =
                                                     let uu____3174 =
                                                       let uu____3177 =
                                                         let uu____3178 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3178 in
                                                       (f_has_t, uu____3177) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3174 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3173) in
                                                 mkForall_fuel uu____3167 in
                                               (uu____3166,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3162 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3191 =
                                               let uu____3195 =
                                                 let uu____3196 =
                                                   let uu____3202 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3202) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3196 in
                                               (uu____3195, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3191 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3216 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3216);
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
                     let uu____3227 =
                       let uu____3231 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3231, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3227 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3240 =
                       let uu____3244 =
                         let uu____3245 =
                           let uu____3251 =
                             let uu____3252 =
                               let uu____3255 =
                                 let uu____3256 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3256 in
                               (f_has_t, uu____3255) in
                             FStar_SMTEncoding_Util.mkImp uu____3252 in
                           ([[f_has_t]], [fsym], uu____3251) in
                         mkForall_fuel uu____3245 in
                       (uu____3244, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3240 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3270 ->
           let uu____3275 =
             let uu____3278 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3278 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3283;
                 FStar_Syntax_Syntax.pos = uu____3284;
                 FStar_Syntax_Syntax.vars = uu____3285;_} ->
                 let uu____3292 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____3292 with
                  | (b,f1) ->
                      let uu____3306 =
                        let uu____3307 = FStar_List.hd b in fst uu____3307 in
                      (uu____3306, f1))
             | uu____3312 -> failwith "impossible" in
           (match uu____3275 with
            | (x,f) ->
                let uu____3319 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3319 with
                 | (base_t,decls) ->
                     let uu____3326 = gen_term_var env x in
                     (match uu____3326 with
                      | (x1,xtm,env') ->
                          let uu____3335 = encode_formula f env' in
                          (match uu____3335 with
                           | (refinement,decls') ->
                               let uu____3342 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3342 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3353 =
                                        let uu____3355 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3359 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3355
                                          uu____3359 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3353 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3375  ->
                                              match uu____3375 with
                                              | (y,uu____3379) ->
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
                                    let uu____3398 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3398 with
                                     | Some cache_entry ->
                                         let uu____3403 =
                                           let uu____3404 =
                                             let uu____3408 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3408) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3404 in
                                         (uu____3403,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3420 =
                                             let uu____3421 =
                                               let uu____3422 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3422 in
                                             Prims.strcat module_name
                                               uu____3421 in
                                           varops.mk_unique uu____3420 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3431 =
                                             let uu____3435 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3435) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3431 in
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
                                           let uu____3446 =
                                             let uu____3450 =
                                               let uu____3451 =
                                                 let uu____3457 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3457) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3451 in
                                             (uu____3450,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3446 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____3472 =
                                             let uu____3476 =
                                               let uu____3477 =
                                                 let uu____3483 =
                                                   let uu____3484 =
                                                     let uu____3487 =
                                                       let uu____3488 =
                                                         let uu____3494 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____3494) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____3488 in
                                                     (uu____3487, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____3484 in
                                                 ([[valid_t]], cvars1,
                                                   uu____3483) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3477 in
                                             (uu____3476,
                                               (Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3472 in
                                         let t_kinding =
                                           let uu____3514 =
                                             let uu____3518 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3518,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3514 in
                                         let t_interp =
                                           let uu____3528 =
                                             let uu____3532 =
                                               let uu____3533 =
                                                 let uu____3539 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3539) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3533 in
                                             let uu____3551 =
                                               let uu____3553 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3553 in
                                             (uu____3532, uu____3551,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3528 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3558 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3558);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3575 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3575 in
           let uu____3576 = encode_term_pred None k env ttm in
           (match uu____3576 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3584 =
                    let uu____3588 =
                      let uu____3589 =
                        let uu____3590 =
                          let uu____3591 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3591 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3590 in
                      varops.mk_unique uu____3589 in
                    (t_has_k, (Some "Uvar typing"), uu____3588) in
                  FStar_SMTEncoding_Util.mkAssume uu____3584 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3594 ->
           let uu____3604 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3604 with
            | (head1,args_e) ->
                let uu____3632 =
                  let uu____3640 =
                    let uu____3641 = FStar_Syntax_Subst.compress head1 in
                    uu____3641.FStar_Syntax_Syntax.n in
                  (uu____3640, args_e) in
                (match uu____3632 with
                 | uu____3651 when head_redex env head1 ->
                     let uu____3659 = whnf env t in
                     encode_term uu____3659 env
                 | uu____3660 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____3673;
                       FStar_Syntax_Syntax.pos = uu____3674;
                       FStar_Syntax_Syntax.vars = uu____3675;_},uu____3676),uu____3677::
                    (v1,uu____3679)::(v2,uu____3681)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3719 = encode_term v1 env in
                     (match uu____3719 with
                      | (v11,decls1) ->
                          let uu____3726 = encode_term v2 env in
                          (match uu____3726 with
                           | (v21,decls2) ->
                               let uu____3733 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3733,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3736::(v1,uu____3738)::(v2,uu____3740)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3774 = encode_term v1 env in
                     (match uu____3774 with
                      | (v11,decls1) ->
                          let uu____3781 = encode_term v2 env in
                          (match uu____3781 with
                           | (v21,decls2) ->
                               let uu____3788 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3788,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3790) ->
                     let e0 =
                       let uu____3802 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3802 in
                     ((let uu____3808 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3808
                       then
                         let uu____3809 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3809
                       else ());
                      (let e =
                         let uu____3814 =
                           let uu____3815 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3816 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3815
                             uu____3816 in
                         uu____3814 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3825),(arg,uu____3827)::[]) -> encode_term arg env
                 | uu____3845 ->
                     let uu____3853 = encode_args args_e env in
                     (match uu____3853 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3886 = encode_term head1 env in
                            match uu____3886 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3925 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3925 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3969  ->
                                                 fun uu____3970  ->
                                                   match (uu____3969,
                                                           uu____3970)
                                                   with
                                                   | ((bv,uu____3984),
                                                      (a,uu____3986)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____4000 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____4000
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____4005 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____4005 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____4015 =
                                                   let uu____4019 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____4024 =
                                                     let uu____4025 =
                                                       let uu____4026 =
                                                         let uu____4027 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____4027 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____4026 in
                                                     varops.mk_unique
                                                       uu____4025 in
                                                   (uu____4019,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____4024) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____4015 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____4044 = lookup_free_var_sym env fv in
                            match uu____4044 with
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
                                   FStar_Syntax_Syntax.tk = uu____4067;
                                   FStar_Syntax_Syntax.pos = uu____4068;
                                   FStar_Syntax_Syntax.vars = uu____4069;_},uu____4070)
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____4081;
                                   FStar_Syntax_Syntax.pos = uu____4082;
                                   FStar_Syntax_Syntax.vars = uu____4083;_},uu____4084)
                                ->
                                let uu____4089 =
                                  let uu____4090 =
                                    let uu____4093 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4093
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4090
                                    FStar_Pervasives.snd in
                                Some uu____4089
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4113 =
                                  let uu____4114 =
                                    let uu____4117 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4117
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4114
                                    FStar_Pervasives.snd in
                                Some uu____4113
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4136,(FStar_Util.Inl t1,uu____4138),uu____4139)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4177,(FStar_Util.Inr c,uu____4179),uu____4180)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4218 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4238 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4238 in
                               let uu____4239 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4239 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4249;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4250;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4251;_},uu____4252)
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
                                     | uu____4284 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4334 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4334 with
            | (bs1,body1,opening) ->
                let fallback uu____4349 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____4354 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4354, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4365 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____4365
                  | FStar_Util.Inr (eff,uu____4367) ->
                      let uu____4373 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____4373 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4418 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___135_4419 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___135_4419.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___135_4419.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___135_4419.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___135_4419.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___135_4419.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___135_4419.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___135_4419.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___135_4419.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___135_4419.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___135_4419.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___135_4419.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___135_4419.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___135_4419.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___135_4419.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___135_4419.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___135_4419.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___135_4419.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___135_4419.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___135_4419.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___135_4419.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___135_4419.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___135_4419.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___135_4419.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___135_4419.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___135_4419.FStar_TypeChecker_Env.synth)
                             }) uu____4418 FStar_Syntax_Syntax.U_unknown in
                        let uu____4420 =
                          let uu____4421 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4421 in
                        FStar_Util.Inl uu____4420
                    | FStar_Util.Inr (eff_name,uu____4428) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4459 =
                        let uu____4460 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4460 in
                      FStar_All.pipe_right uu____4459
                        (fun _0_41  -> Some _0_41)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4472 =
                        let uu____4473 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4473 FStar_Pervasives.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4481 =
                          let uu____4482 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4482 in
                        FStar_All.pipe_right uu____4481
                          (fun _0_42  -> Some _0_42)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4486 =
                             let uu____4487 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4487 in
                           FStar_All.pipe_right uu____4486
                             (fun _0_43  -> Some _0_43))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4498 =
                         let uu____4499 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4499 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4498);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4514 =
                       (is_impure lc1) &&
                         (let uu____4515 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4515) in
                     if uu____4514
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4520 = encode_binders None bs1 env in
                        match uu____4520 with
                        | (vars,guards,envbody,decls,uu____4535) ->
                            let uu____4542 =
                              let uu____4550 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4550
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4542 with
                             | (lc2,body2) ->
                                 let uu____4575 = encode_term body2 envbody in
                                 (match uu____4575 with
                                  | (body3,decls') ->
                                      let uu____4582 =
                                        let uu____4587 = codomain_eff lc2 in
                                        match uu____4587 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4599 =
                                              encode_term tfun env in
                                            (match uu____4599 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4582 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4618 =
                                               let uu____4624 =
                                                 let uu____4625 =
                                                   let uu____4628 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4628, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4625 in
                                               ([], vars, uu____4624) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4618 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4636 =
                                                   let uu____4638 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4638 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4636 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4649 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4649 with
                                            | Some cache_entry ->
                                                let uu____4654 =
                                                  let uu____4655 =
                                                    let uu____4659 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4659) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4655 in
                                                (uu____4654,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | None  ->
                                                let uu____4665 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4665 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4672 =
                                                         let uu____4673 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4673 =
                                                           cache_size in
                                                       if uu____4672
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
                                                         let uu____4684 =
                                                           let uu____4685 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4685 in
                                                         varops.mk_unique
                                                           uu____4684 in
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
                                                       let uu____4690 =
                                                         let uu____4694 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4694) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4690 in
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
                                                           let uu____4706 =
                                                             let uu____4707 =
                                                               let uu____4711
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4711,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4707 in
                                                           [uu____4706] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4719 =
                                                         let uu____4723 =
                                                           let uu____4724 =
                                                             let uu____4730 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4730) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4724 in
                                                         (uu____4723,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4719 in
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
                                                     ((let uu____4740 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4740);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4742,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4743;
                          FStar_Syntax_Syntax.lbunivs = uu____4744;
                          FStar_Syntax_Syntax.lbtyp = uu____4745;
                          FStar_Syntax_Syntax.lbeff = uu____4746;
                          FStar_Syntax_Syntax.lbdef = uu____4747;_}::uu____4748),uu____4749)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4767;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4769;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4785 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4798 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4798, [decl_e])))
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
              let uu____4840 = encode_term e1 env in
              match uu____4840 with
              | (ee1,decls1) ->
                  let uu____4847 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4847 with
                   | (xs,e21) ->
                       let uu____4861 = FStar_List.hd xs in
                       (match uu____4861 with
                        | (x1,uu____4869) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4871 = encode_body e21 env' in
                            (match uu____4871 with
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
            let uu____4893 =
              let uu____4897 =
                let uu____4898 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4898 in
              gen_term_var env uu____4897 in
            match uu____4893 with
            | (scrsym,scr',env1) ->
                let uu____4908 = encode_term e env1 in
                (match uu____4908 with
                 | (scr,decls) ->
                     let uu____4915 =
                       let encode_branch b uu____4931 =
                         match uu____4931 with
                         | (else_case,decls1) ->
                             let uu____4942 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4942 with
                              | (p,w,br) ->
                                  let uu____4963 = encode_pat env1 p in
                                  (match uu____4963 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____4983  ->
                                                   match uu____4983 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____4988 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____5003 =
                                               encode_term w1 env2 in
                                             (match uu____5003 with
                                              | (w2,decls2) ->
                                                  let uu____5011 =
                                                    let uu____5012 =
                                                      let uu____5015 =
                                                        let uu____5016 =
                                                          let uu____5019 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____5019) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____5016 in
                                                      (guard, uu____5015) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____5012 in
                                                  (uu____5011, decls2)) in
                                       (match uu____4988 with
                                        | (guard1,decls2) ->
                                            let uu____5027 =
                                              encode_br br env2 in
                                            (match uu____5027 with
                                             | (br1,decls3) ->
                                                 let uu____5035 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____5035,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4915 with
                      | (match_tm,decls1) ->
                          let uu____5046 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____5046, decls1)))
and encode_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____5068 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5068
       then
         let uu____5069 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5069
       else ());
      (let uu____5071 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5071 with
       | (vars,pat_term) ->
           let uu____5081 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5104  ->
                     fun v1  ->
                       match uu____5104 with
                       | (env1,vars1) ->
                           let uu____5132 = gen_term_var env1 v1 in
                           (match uu____5132 with
                            | (xx,uu____5144,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____5081 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5191 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5192 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5193 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5199 =
                        let uu____5202 = encode_const c in
                        (scrutinee, uu____5202) in
                      FStar_SMTEncoding_Util.mkEq uu____5199
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5221 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5221 with
                        | (uu____5225,uu____5226::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5228 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5249  ->
                                  match uu____5249 with
                                  | (arg,uu____5255) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5265 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5265)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5285) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5304 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5319 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5341  ->
                                  match uu____5341 with
                                  | (arg,uu____5350) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5360 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5360)) in
                      FStar_All.pipe_right uu____5319 FStar_List.flatten in
                let pat_term1 uu____5376 = encode_term pat_term env1 in
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
      let uu____5383 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5398  ->
                fun uu____5399  ->
                  match (uu____5398, uu____5399) with
                  | ((tms,decls),(t,uu____5419)) ->
                      let uu____5430 = encode_term t env in
                      (match uu____5430 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5383 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5464 = FStar_Syntax_Util.list_elements e in
        match uu____5464 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5479 =
          let uu____5489 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5489 FStar_Syntax_Util.head_and_args in
        match uu____5479 with
        | (head1,args) ->
            let uu____5517 =
              let uu____5525 =
                let uu____5526 = FStar_Syntax_Util.un_uinst head1 in
                uu____5526.FStar_Syntax_Syntax.n in
              (uu____5525, args) in
            (match uu____5517 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5537,uu____5538)::(e,uu____5540)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> e
             | uu____5566 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____5593 =
            let uu____5603 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5603 FStar_Syntax_Util.head_and_args in
          match uu____5593 with
          | (head1,args) ->
              let uu____5632 =
                let uu____5640 =
                  let uu____5641 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5641.FStar_Syntax_Syntax.n in
                (uu____5640, args) in
              (match uu____5632 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5654)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5674 -> None) in
        match elts with
        | t1::[] ->
            let uu____5689 = smt_pat_or1 t1 in
            (match uu____5689 with
             | Some e ->
                 let uu____5702 = list_elements1 e in
                 FStar_All.pipe_right uu____5702
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5713 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5713
                           (FStar_List.map one_pat)))
             | uu____5721 ->
                 let uu____5725 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5725])
        | uu____5741 ->
            let uu____5743 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5743] in
      let uu____5759 =
        let uu____5772 =
          let uu____5773 = FStar_Syntax_Subst.compress t in
          uu____5773.FStar_Syntax_Syntax.n in
        match uu____5772 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5800 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5800 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5829;
                        FStar_Syntax_Syntax.effect_name = uu____5830;
                        FStar_Syntax_Syntax.result_typ = uu____5831;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5833)::(post,uu____5835)::(pats,uu____5837)::[];
                        FStar_Syntax_Syntax.flags = uu____5838;_}
                      ->
                      let uu____5870 = lemma_pats pats in
                      (binders1, pre, post, uu____5870)
                  | uu____5883 -> failwith "impos"))
        | uu____5896 -> failwith "Impos" in
      match uu____5759 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___136_5932 = env in
            {
              bindings = (uu___136_5932.bindings);
              depth = (uu___136_5932.depth);
              tcenv = (uu___136_5932.tcenv);
              warn = (uu___136_5932.warn);
              cache = (uu___136_5932.cache);
              nolabels = (uu___136_5932.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___136_5932.encode_non_total_function_typ);
              current_module_name = (uu___136_5932.current_module_name)
            } in
          let uu____5933 = encode_binders None binders env1 in
          (match uu____5933 with
           | (vars,guards,env2,decls,uu____5948) ->
               let uu____5955 =
                 let uu____5962 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____5984 =
                             let uu____5989 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____5989 FStar_List.unzip in
                           match uu____5984 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____5962 FStar_List.unzip in
               (match uu____5955 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___137_6047 = env2 in
                      {
                        bindings = (uu___137_6047.bindings);
                        depth = (uu___137_6047.depth);
                        tcenv = (uu___137_6047.tcenv);
                        warn = (uu___137_6047.warn);
                        cache = (uu___137_6047.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___137_6047.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___137_6047.encode_non_total_function_typ);
                        current_module_name =
                          (uu___137_6047.current_module_name)
                      } in
                    let uu____6048 =
                      let uu____6051 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6051 env3 in
                    (match uu____6048 with
                     | (pre1,decls'') ->
                         let uu____6056 =
                           let uu____6059 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6059 env3 in
                         (match uu____6056 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6066 =
                                let uu____6067 =
                                  let uu____6073 =
                                    let uu____6074 =
                                      let uu____6077 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6077, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6074 in
                                  (pats, vars, uu____6073) in
                                FStar_SMTEncoding_Util.mkForall uu____6067 in
                              (uu____6066, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6090 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6090
        then
          let uu____6091 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6092 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6091 uu____6092
        else () in
      let enc f r l =
        let uu____6119 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6132 = encode_term (fst x) env in
                 match uu____6132 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6119 with
        | (decls,args) ->
            let uu____6149 =
              let uu___138_6150 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___138_6150.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___138_6150.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6149, decls) in
      let const_op f r uu____6175 = let uu____6184 = f r in (uu____6184, []) in
      let un_op f l =
        let uu____6200 = FStar_List.hd l in FStar_All.pipe_left f uu____6200 in
      let bin_op f uu___111_6213 =
        match uu___111_6213 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6221 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6248 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6257  ->
                 match uu____6257 with
                 | (t,uu____6265) ->
                     let uu____6266 = encode_formula t env in
                     (match uu____6266 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6248 with
        | (decls,phis) ->
            let uu____6283 =
              let uu___139_6284 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6284.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6284.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6283, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____6323  ->
               match uu____6323 with
               | (a,q) ->
                   (match q with
                    | Some (FStar_Syntax_Syntax.Implicit uu____6337) -> false
                    | uu____6338 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____6351 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____6351
        else
          (let uu____6366 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____6366 r rf) in
      let mk_imp1 r uu___112_6385 =
        match uu___112_6385 with
        | (lhs,uu____6389)::(rhs,uu____6391)::[] ->
            let uu____6412 = encode_formula rhs env in
            (match uu____6412 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6421) ->
                      (l1, decls1)
                  | uu____6424 ->
                      let uu____6425 = encode_formula lhs env in
                      (match uu____6425 with
                       | (l2,decls2) ->
                           let uu____6432 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6432, (FStar_List.append decls1 decls2)))))
        | uu____6434 -> failwith "impossible" in
      let mk_ite r uu___113_6449 =
        match uu___113_6449 with
        | (guard,uu____6453)::(_then,uu____6455)::(_else,uu____6457)::[] ->
            let uu____6486 = encode_formula guard env in
            (match uu____6486 with
             | (g,decls1) ->
                 let uu____6493 = encode_formula _then env in
                 (match uu____6493 with
                  | (t,decls2) ->
                      let uu____6500 = encode_formula _else env in
                      (match uu____6500 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6509 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6528 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6528 in
      let connectives =
        let uu____6540 =
          let uu____6549 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6549) in
        let uu____6562 =
          let uu____6572 =
            let uu____6581 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6581) in
          let uu____6594 =
            let uu____6604 =
              let uu____6614 =
                let uu____6623 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6623) in
              let uu____6636 =
                let uu____6646 =
                  let uu____6656 =
                    let uu____6665 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6665) in
                  [uu____6656;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6646 in
              uu____6614 :: uu____6636 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6604 in
          uu____6572 :: uu____6594 in
        uu____6540 :: uu____6562 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6881 = encode_formula phi' env in
            (match uu____6881 with
             | (phi2,decls) ->
                 let uu____6888 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6888, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6889 ->
            let uu____6894 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6894 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6923 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6923 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6931;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6933;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6949 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6949 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6981::(x,uu____6983)::(t,uu____6985)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____7019 = encode_term x env in
                 (match uu____7019 with
                  | (x1,decls) ->
                      let uu____7026 = encode_term t env in
                      (match uu____7026 with
                       | (t1,decls') ->
                           let uu____7033 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____7033, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____7037)::(msg,uu____7039)::(phi2,uu____7041)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____7075 =
                   let uu____7078 =
                     let uu____7079 = FStar_Syntax_Subst.compress r in
                     uu____7079.FStar_Syntax_Syntax.n in
                   let uu____7082 =
                     let uu____7083 = FStar_Syntax_Subst.compress msg in
                     uu____7083.FStar_Syntax_Syntax.n in
                   (uu____7078, uu____7082) in
                 (match uu____7075 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7090))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____7106 -> fallback phi2)
             | uu____7109 when head_redex env head2 ->
                 let uu____7117 = whnf env phi1 in
                 encode_formula uu____7117 env
             | uu____7118 ->
                 let uu____7126 = encode_term phi1 env in
                 (match uu____7126 with
                  | (tt,decls) ->
                      let uu____7133 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___140_7134 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___140_7134.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___140_7134.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7133, decls)))
        | uu____7137 ->
            let uu____7138 = encode_term phi1 env in
            (match uu____7138 with
             | (tt,decls) ->
                 let uu____7145 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___141_7146 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___141_7146.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___141_7146.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7145, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7173 = encode_binders None bs env1 in
        match uu____7173 with
        | (vars,guards,env2,decls,uu____7195) ->
            let uu____7202 =
              let uu____7209 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7232 =
                          let uu____7237 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7251  ->
                                    match uu____7251 with
                                    | (t,uu____7257) ->
                                        encode_term t
                                          (let uu___142_7258 = env2 in
                                           {
                                             bindings =
                                               (uu___142_7258.bindings);
                                             depth = (uu___142_7258.depth);
                                             tcenv = (uu___142_7258.tcenv);
                                             warn = (uu___142_7258.warn);
                                             cache = (uu___142_7258.cache);
                                             nolabels =
                                               (uu___142_7258.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___142_7258.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___142_7258.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7237 FStar_List.unzip in
                        match uu____7232 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7209 FStar_List.unzip in
            (match uu____7202 with
             | (pats,decls') ->
                 let uu____7310 = encode_formula body env2 in
                 (match uu____7310 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7329;
                             FStar_SMTEncoding_Term.rng = uu____7330;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7338 -> guards in
                      let uu____7341 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7341, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7375  ->
                   match uu____7375 with
                   | (x,uu____7379) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7385 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7391 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7391) uu____7385 tl1 in
             let uu____7393 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7405  ->
                       match uu____7405 with
                       | (b,uu____7409) ->
                           let uu____7410 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7410)) in
             (match uu____7393 with
              | None  -> ()
              | Some (x,uu____7414) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7424 =
                    let uu____7425 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7425 in
                  FStar_Errors.warn pos uu____7424) in
       let uu____7426 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7426 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7432 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7468  ->
                     match uu____7468 with
                     | (l,uu____7478) -> FStar_Ident.lid_equals op l)) in
           (match uu____7432 with
            | None  -> fallback phi1
            | Some (uu____7501,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7530 = encode_q_body env vars pats body in
             match uu____7530 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7556 =
                     let uu____7562 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7562) in
                   FStar_SMTEncoding_Term.mkForall uu____7556
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7574 = encode_q_body env vars pats body in
             match uu____7574 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7599 =
                   let uu____7600 =
                     let uu____7606 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7606) in
                   FStar_SMTEncoding_Term.mkExists uu____7600
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7599, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7660 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7660 with
  | (asym,a) ->
      let uu____7665 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7665 with
       | (xsym,x) ->
           let uu____7670 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7670 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7700 =
                      let uu____7706 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____7706, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7700 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7721 =
                      let uu____7725 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7725) in
                    FStar_SMTEncoding_Util.mkApp uu____7721 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7733 =
                    let uu____7735 =
                      let uu____7737 =
                        let uu____7739 =
                          let uu____7740 =
                            let uu____7744 =
                              let uu____7745 =
                                let uu____7751 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7751) in
                              FStar_SMTEncoding_Util.mkForall uu____7745 in
                            (uu____7744, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7740 in
                        let uu____7760 =
                          let uu____7762 =
                            let uu____7763 =
                              let uu____7767 =
                                let uu____7768 =
                                  let uu____7774 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7774) in
                                FStar_SMTEncoding_Util.mkForall uu____7768 in
                              (uu____7767,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7763 in
                          [uu____7762] in
                        uu____7739 :: uu____7760 in
                      xtok_decl :: uu____7737 in
                    xname_decl :: uu____7735 in
                  (xtok1, uu____7733) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7823 =
                    let uu____7831 =
                      let uu____7837 =
                        let uu____7838 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7838 in
                      quant axy uu____7837 in
                    (FStar_Syntax_Const.op_Eq, uu____7831) in
                  let uu____7844 =
                    let uu____7853 =
                      let uu____7861 =
                        let uu____7867 =
                          let uu____7868 =
                            let uu____7869 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7869 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7868 in
                        quant axy uu____7867 in
                      (FStar_Syntax_Const.op_notEq, uu____7861) in
                    let uu____7875 =
                      let uu____7884 =
                        let uu____7892 =
                          let uu____7898 =
                            let uu____7899 =
                              let uu____7900 =
                                let uu____7903 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7904 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7903, uu____7904) in
                              FStar_SMTEncoding_Util.mkLT uu____7900 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7899 in
                          quant xy uu____7898 in
                        (FStar_Syntax_Const.op_LT, uu____7892) in
                      let uu____7910 =
                        let uu____7919 =
                          let uu____7927 =
                            let uu____7933 =
                              let uu____7934 =
                                let uu____7935 =
                                  let uu____7938 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7939 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7938, uu____7939) in
                                FStar_SMTEncoding_Util.mkLTE uu____7935 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7934 in
                            quant xy uu____7933 in
                          (FStar_Syntax_Const.op_LTE, uu____7927) in
                        let uu____7945 =
                          let uu____7954 =
                            let uu____7962 =
                              let uu____7968 =
                                let uu____7969 =
                                  let uu____7970 =
                                    let uu____7973 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7974 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7973, uu____7974) in
                                  FStar_SMTEncoding_Util.mkGT uu____7970 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7969 in
                              quant xy uu____7968 in
                            (FStar_Syntax_Const.op_GT, uu____7962) in
                          let uu____7980 =
                            let uu____7989 =
                              let uu____7997 =
                                let uu____8003 =
                                  let uu____8004 =
                                    let uu____8005 =
                                      let uu____8008 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____8009 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____8008, uu____8009) in
                                    FStar_SMTEncoding_Util.mkGTE uu____8005 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____8004 in
                                quant xy uu____8003 in
                              (FStar_Syntax_Const.op_GTE, uu____7997) in
                            let uu____8015 =
                              let uu____8024 =
                                let uu____8032 =
                                  let uu____8038 =
                                    let uu____8039 =
                                      let uu____8040 =
                                        let uu____8043 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____8044 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____8043, uu____8044) in
                                      FStar_SMTEncoding_Util.mkSub uu____8040 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8039 in
                                  quant xy uu____8038 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____8032) in
                              let uu____8050 =
                                let uu____8059 =
                                  let uu____8067 =
                                    let uu____8073 =
                                      let uu____8074 =
                                        let uu____8075 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8075 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8074 in
                                    quant qx uu____8073 in
                                  (FStar_Syntax_Const.op_Minus, uu____8067) in
                                let uu____8081 =
                                  let uu____8090 =
                                    let uu____8098 =
                                      let uu____8104 =
                                        let uu____8105 =
                                          let uu____8106 =
                                            let uu____8109 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8110 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8109, uu____8110) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8106 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8105 in
                                      quant xy uu____8104 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8098) in
                                  let uu____8116 =
                                    let uu____8125 =
                                      let uu____8133 =
                                        let uu____8139 =
                                          let uu____8140 =
                                            let uu____8141 =
                                              let uu____8144 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8145 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8144, uu____8145) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8141 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8140 in
                                        quant xy uu____8139 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8133) in
                                    let uu____8151 =
                                      let uu____8160 =
                                        let uu____8168 =
                                          let uu____8174 =
                                            let uu____8175 =
                                              let uu____8176 =
                                                let uu____8179 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8180 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8179, uu____8180) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8176 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8175 in
                                          quant xy uu____8174 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8168) in
                                      let uu____8186 =
                                        let uu____8195 =
                                          let uu____8203 =
                                            let uu____8209 =
                                              let uu____8210 =
                                                let uu____8211 =
                                                  let uu____8214 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8215 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8214, uu____8215) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8211 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8210 in
                                            quant xy uu____8209 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8203) in
                                        let uu____8221 =
                                          let uu____8230 =
                                            let uu____8238 =
                                              let uu____8244 =
                                                let uu____8245 =
                                                  let uu____8246 =
                                                    let uu____8249 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8250 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8249, uu____8250) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8246 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8245 in
                                              quant xy uu____8244 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8238) in
                                          let uu____8256 =
                                            let uu____8265 =
                                              let uu____8273 =
                                                let uu____8279 =
                                                  let uu____8280 =
                                                    let uu____8281 =
                                                      let uu____8284 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8285 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8284,
                                                        uu____8285) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8281 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8280 in
                                                quant xy uu____8279 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8273) in
                                            let uu____8291 =
                                              let uu____8300 =
                                                let uu____8308 =
                                                  let uu____8314 =
                                                    let uu____8315 =
                                                      let uu____8316 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8316 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8315 in
                                                  quant qx uu____8314 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8308) in
                                              [uu____8300] in
                                            uu____8265 :: uu____8291 in
                                          uu____8230 :: uu____8256 in
                                        uu____8195 :: uu____8221 in
                                      uu____8160 :: uu____8186 in
                                    uu____8125 :: uu____8151 in
                                  uu____8090 :: uu____8116 in
                                uu____8059 :: uu____8081 in
                              uu____8024 :: uu____8050 in
                            uu____7989 :: uu____8015 in
                          uu____7954 :: uu____7980 in
                        uu____7919 :: uu____7945 in
                      uu____7884 :: uu____7910 in
                    uu____7853 :: uu____7875 in
                  uu____7823 :: uu____7844 in
                let mk1 l v1 =
                  let uu____8444 =
                    let uu____8449 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8481  ->
                              match uu____8481 with
                              | (l',uu____8490) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8449
                      (FStar_Option.map
                         (fun uu____8523  ->
                            match uu____8523 with | (uu____8534,b) -> b v1)) in
                  FStar_All.pipe_right uu____8444 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8575  ->
                          match uu____8575 with
                          | (l',uu____8584) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8610 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8610 with
        | (xxsym,xx) ->
            let uu____8615 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8615 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8623 =
                   let uu____8627 =
                     let uu____8628 =
                       let uu____8634 =
                         let uu____8635 =
                           let uu____8638 =
                             let uu____8639 =
                               let uu____8642 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8642) in
                             FStar_SMTEncoding_Util.mkEq uu____8639 in
                           (xx_has_type, uu____8638) in
                         FStar_SMTEncoding_Util.mkImp uu____8635 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8634) in
                     FStar_SMTEncoding_Util.mkForall uu____8628 in
                   let uu____8655 =
                     let uu____8656 =
                       let uu____8657 =
                         let uu____8658 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8658 in
                       Prims.strcat module_name uu____8657 in
                     varops.mk_unique uu____8656 in
                   (uu____8627, (Some "pretyping"), uu____8655) in
                 FStar_SMTEncoding_Util.mkAssume uu____8623)
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
    let uu____8688 =
      let uu____8689 =
        let uu____8693 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8693, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8689 in
    let uu____8695 =
      let uu____8697 =
        let uu____8698 =
          let uu____8702 =
            let uu____8703 =
              let uu____8709 =
                let uu____8710 =
                  let uu____8713 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8713) in
                FStar_SMTEncoding_Util.mkImp uu____8710 in
              ([[typing_pred]], [xx], uu____8709) in
            mkForall_fuel uu____8703 in
          (uu____8702, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8698 in
      [uu____8697] in
    uu____8688 :: uu____8695 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8741 =
      let uu____8742 =
        let uu____8746 =
          let uu____8747 =
            let uu____8753 =
              let uu____8756 =
                let uu____8758 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8758] in
              [uu____8756] in
            let uu____8761 =
              let uu____8762 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8762 tt in
            (uu____8753, [bb], uu____8761) in
          FStar_SMTEncoding_Util.mkForall uu____8747 in
        (uu____8746, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8742 in
    let uu____8773 =
      let uu____8775 =
        let uu____8776 =
          let uu____8780 =
            let uu____8781 =
              let uu____8787 =
                let uu____8788 =
                  let uu____8791 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8791) in
                FStar_SMTEncoding_Util.mkImp uu____8788 in
              ([[typing_pred]], [xx], uu____8787) in
            mkForall_fuel uu____8781 in
          (uu____8780, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8776 in
      [uu____8775] in
    uu____8741 :: uu____8773 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8825 =
        let uu____8826 =
          let uu____8830 =
            let uu____8832 =
              let uu____8834 =
                let uu____8836 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8837 =
                  let uu____8839 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8839] in
                uu____8836 :: uu____8837 in
              tt :: uu____8834 in
            tt :: uu____8832 in
          ("Prims.Precedes", uu____8830) in
        FStar_SMTEncoding_Util.mkApp uu____8826 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8825 in
    let precedes_y_x =
      let uu____8842 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8842 in
    let uu____8844 =
      let uu____8845 =
        let uu____8849 =
          let uu____8850 =
            let uu____8856 =
              let uu____8859 =
                let uu____8861 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8861] in
              [uu____8859] in
            let uu____8864 =
              let uu____8865 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8865 tt in
            (uu____8856, [bb], uu____8864) in
          FStar_SMTEncoding_Util.mkForall uu____8850 in
        (uu____8849, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8845 in
    let uu____8876 =
      let uu____8878 =
        let uu____8879 =
          let uu____8883 =
            let uu____8884 =
              let uu____8890 =
                let uu____8891 =
                  let uu____8894 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8894) in
                FStar_SMTEncoding_Util.mkImp uu____8891 in
              ([[typing_pred]], [xx], uu____8890) in
            mkForall_fuel uu____8884 in
          (uu____8883, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8879 in
      let uu____8907 =
        let uu____8909 =
          let uu____8910 =
            let uu____8914 =
              let uu____8915 =
                let uu____8921 =
                  let uu____8922 =
                    let uu____8925 =
                      let uu____8926 =
                        let uu____8928 =
                          let uu____8930 =
                            let uu____8932 =
                              let uu____8933 =
                                let uu____8936 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8937 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8936, uu____8937) in
                              FStar_SMTEncoding_Util.mkGT uu____8933 in
                            let uu____8938 =
                              let uu____8940 =
                                let uu____8941 =
                                  let uu____8944 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8945 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8944, uu____8945) in
                                FStar_SMTEncoding_Util.mkGTE uu____8941 in
                              let uu____8946 =
                                let uu____8948 =
                                  let uu____8949 =
                                    let uu____8952 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8953 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8952, uu____8953) in
                                  FStar_SMTEncoding_Util.mkLT uu____8949 in
                                [uu____8948] in
                              uu____8940 :: uu____8946 in
                            uu____8932 :: uu____8938 in
                          typing_pred_y :: uu____8930 in
                        typing_pred :: uu____8928 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8926 in
                    (uu____8925, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8922 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8921) in
              mkForall_fuel uu____8915 in
            (uu____8914, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8910 in
        [uu____8909] in
      uu____8878 :: uu____8907 in
    uu____8844 :: uu____8876 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8983 =
      let uu____8984 =
        let uu____8988 =
          let uu____8989 =
            let uu____8995 =
              let uu____8998 =
                let uu____9000 = FStar_SMTEncoding_Term.boxString b in
                [uu____9000] in
              [uu____8998] in
            let uu____9003 =
              let uu____9004 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____9004 tt in
            (uu____8995, [bb], uu____9003) in
          FStar_SMTEncoding_Util.mkForall uu____8989 in
        (uu____8988, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8984 in
    let uu____9015 =
      let uu____9017 =
        let uu____9018 =
          let uu____9022 =
            let uu____9023 =
              let uu____9029 =
                let uu____9030 =
                  let uu____9033 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____9033) in
                FStar_SMTEncoding_Util.mkImp uu____9030 in
              ([[typing_pred]], [xx], uu____9029) in
            mkForall_fuel uu____9023 in
          (uu____9022, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9018 in
      [uu____9017] in
    uu____8983 :: uu____9015 in
  let mk_ref1 env reft_name uu____9055 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____9066 =
        let uu____9070 =
          let uu____9072 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9072] in
        (reft_name, uu____9070) in
      FStar_SMTEncoding_Util.mkApp uu____9066 in
    let refb =
      let uu____9075 =
        let uu____9079 =
          let uu____9081 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9081] in
        (reft_name, uu____9079) in
      FStar_SMTEncoding_Util.mkApp uu____9075 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9085 =
      let uu____9086 =
        let uu____9090 =
          let uu____9091 =
            let uu____9097 =
              let uu____9098 =
                let uu____9101 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9101) in
              FStar_SMTEncoding_Util.mkImp uu____9098 in
            ([[typing_pred]], [xx; aa], uu____9097) in
          mkForall_fuel uu____9091 in
        (uu____9090, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9086 in
    [uu____9085] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9141 =
      let uu____9142 =
        let uu____9146 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9146, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9142 in
    [uu____9141] in
  let mk_and_interp env conj uu____9157 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9174 =
      let uu____9175 =
        let uu____9179 =
          let uu____9180 =
            let uu____9186 =
              let uu____9187 =
                let uu____9190 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9190, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9187 in
            ([[l_and_a_b]], [aa; bb], uu____9186) in
          FStar_SMTEncoding_Util.mkForall uu____9180 in
        (uu____9179, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9175 in
    [uu____9174] in
  let mk_or_interp env disj uu____9214 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9231 =
      let uu____9232 =
        let uu____9236 =
          let uu____9237 =
            let uu____9243 =
              let uu____9244 =
                let uu____9247 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9247, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9244 in
            ([[l_or_a_b]], [aa; bb], uu____9243) in
          FStar_SMTEncoding_Util.mkForall uu____9237 in
        (uu____9236, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9232 in
    [uu____9231] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9288 =
      let uu____9289 =
        let uu____9293 =
          let uu____9294 =
            let uu____9300 =
              let uu____9301 =
                let uu____9304 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9304, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9301 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9300) in
          FStar_SMTEncoding_Util.mkForall uu____9294 in
        (uu____9293, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9289 in
    [uu____9288] in
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
    let uu____9351 =
      let uu____9352 =
        let uu____9356 =
          let uu____9357 =
            let uu____9363 =
              let uu____9364 =
                let uu____9367 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9367, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9364 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9363) in
          FStar_SMTEncoding_Util.mkForall uu____9357 in
        (uu____9356, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9352 in
    [uu____9351] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9412 =
      let uu____9413 =
        let uu____9417 =
          let uu____9418 =
            let uu____9424 =
              let uu____9425 =
                let uu____9428 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9428, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9425 in
            ([[l_imp_a_b]], [aa; bb], uu____9424) in
          FStar_SMTEncoding_Util.mkForall uu____9418 in
        (uu____9417, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9413 in
    [uu____9412] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9469 =
      let uu____9470 =
        let uu____9474 =
          let uu____9475 =
            let uu____9481 =
              let uu____9482 =
                let uu____9485 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9485, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9482 in
            ([[l_iff_a_b]], [aa; bb], uu____9481) in
          FStar_SMTEncoding_Util.mkForall uu____9475 in
        (uu____9474, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9470 in
    [uu____9469] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9519 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9519 in
    let uu____9521 =
      let uu____9522 =
        let uu____9526 =
          let uu____9527 =
            let uu____9533 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9533) in
          FStar_SMTEncoding_Util.mkForall uu____9527 in
        (uu____9526, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9522 in
    [uu____9521] in
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
      let uu____9573 =
        let uu____9577 =
          let uu____9579 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9579] in
        ("Valid", uu____9577) in
      FStar_SMTEncoding_Util.mkApp uu____9573 in
    let uu____9581 =
      let uu____9582 =
        let uu____9586 =
          let uu____9587 =
            let uu____9593 =
              let uu____9594 =
                let uu____9597 =
                  let uu____9598 =
                    let uu____9604 =
                      let uu____9607 =
                        let uu____9609 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9609] in
                      [uu____9607] in
                    let uu____9612 =
                      let uu____9613 =
                        let uu____9616 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9616, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9613 in
                    (uu____9604, [xx1], uu____9612) in
                  FStar_SMTEncoding_Util.mkForall uu____9598 in
                (uu____9597, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9594 in
            ([[l_forall_a_b]], [aa; bb], uu____9593) in
          FStar_SMTEncoding_Util.mkForall uu____9587 in
        (uu____9586, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9582 in
    [uu____9581] in
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
      let uu____9667 =
        let uu____9671 =
          let uu____9673 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9673] in
        ("Valid", uu____9671) in
      FStar_SMTEncoding_Util.mkApp uu____9667 in
    let uu____9675 =
      let uu____9676 =
        let uu____9680 =
          let uu____9681 =
            let uu____9687 =
              let uu____9688 =
                let uu____9691 =
                  let uu____9692 =
                    let uu____9698 =
                      let uu____9701 =
                        let uu____9703 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9703] in
                      [uu____9701] in
                    let uu____9706 =
                      let uu____9707 =
                        let uu____9710 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9710, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9707 in
                    (uu____9698, [xx1], uu____9706) in
                  FStar_SMTEncoding_Util.mkExists uu____9692 in
                (uu____9691, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9688 in
            ([[l_exists_a_b]], [aa; bb], uu____9687) in
          FStar_SMTEncoding_Util.mkForall uu____9681 in
        (uu____9680, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9676 in
    [uu____9675] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9746 =
      let uu____9747 =
        let uu____9751 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9752 = varops.mk_unique "typing_range_const" in
        (uu____9751, (Some "Range_const typing"), uu____9752) in
      FStar_SMTEncoding_Util.mkAssume uu____9747 in
    [uu____9746] in
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
          let uu____10014 =
            FStar_Util.find_opt
              (fun uu____10032  ->
                 match uu____10032 with
                 | (l,uu____10042) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____10014 with
          | None  -> []
          | Some (uu____10064,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10101 = encode_function_type_as_formula t env in
        match uu____10101 with
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
            let uu____10133 =
              (let uu____10134 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10134) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10133
            then
              let uu____10138 = new_term_constant_and_tok_from_lid env lid in
              match uu____10138 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10150 =
                      let uu____10151 = FStar_Syntax_Subst.compress t_norm in
                      uu____10151.FStar_Syntax_Syntax.n in
                    match uu____10150 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10156) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10173  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10176 -> [] in
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
              (let uu____10185 = prims.is lid in
               if uu____10185
               then
                 let vname = varops.new_fvar lid in
                 let uu____10190 = prims.mk lid vname in
                 match uu____10190 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10205 =
                    let uu____10211 = curried_arrow_formals_comp t_norm in
                    match uu____10211 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10222 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10222
                          then
                            let uu____10223 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___143_10224 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___143_10224.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___143_10224.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___143_10224.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___143_10224.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___143_10224.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___143_10224.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___143_10224.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___143_10224.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___143_10224.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___143_10224.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___143_10224.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___143_10224.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___143_10224.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___143_10224.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___143_10224.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___143_10224.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___143_10224.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___143_10224.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___143_10224.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___143_10224.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___143_10224.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___143_10224.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___143_10224.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___143_10224.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___143_10224.FStar_TypeChecker_Env.synth)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10223
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10231 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10231)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10205 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10258 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10258 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10271 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___114_10295  ->
                                     match uu___114_10295 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10298 =
                                           FStar_Util.prefix vars in
                                         (match uu____10298 with
                                          | (uu____10309,(xxsym,uu____10311))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10321 =
                                                let uu____10322 =
                                                  let uu____10326 =
                                                    let uu____10327 =
                                                      let uu____10333 =
                                                        let uu____10334 =
                                                          let uu____10337 =
                                                            let uu____10338 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10338 in
                                                          (vapp, uu____10337) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10334 in
                                                      ([[vapp]], vars,
                                                        uu____10333) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10327 in
                                                  (uu____10326,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10322 in
                                              [uu____10321])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10349 =
                                           FStar_Util.prefix vars in
                                         (match uu____10349 with
                                          | (uu____10360,(xxsym,uu____10362))
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
                                              let uu____10376 =
                                                let uu____10377 =
                                                  let uu____10381 =
                                                    let uu____10382 =
                                                      let uu____10388 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10388) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10382 in
                                                  (uu____10381,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10377 in
                                              [uu____10376])
                                     | uu____10397 -> [])) in
                           let uu____10398 = encode_binders None formals env1 in
                           (match uu____10398 with
                            | (vars,guards,env',decls1,uu____10414) ->
                                let uu____10421 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10426 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10426, decls1)
                                  | Some p ->
                                      let uu____10428 = encode_formula p env' in
                                      (match uu____10428 with
                                       | (g,ds) ->
                                           let uu____10435 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10435,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10421 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10444 =
                                         let uu____10448 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10448) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10444 in
                                     let uu____10453 =
                                       let vname_decl =
                                         let uu____10458 =
                                           let uu____10464 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10469  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10464,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10458 in
                                       let uu____10474 =
                                         let env2 =
                                           let uu___144_10478 = env1 in
                                           {
                                             bindings =
                                               (uu___144_10478.bindings);
                                             depth = (uu___144_10478.depth);
                                             tcenv = (uu___144_10478.tcenv);
                                             warn = (uu___144_10478.warn);
                                             cache = (uu___144_10478.cache);
                                             nolabels =
                                               (uu___144_10478.nolabels);
                                             use_zfuel_name =
                                               (uu___144_10478.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___144_10478.current_module_name)
                                           } in
                                         let uu____10479 =
                                           let uu____10480 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10480 in
                                         if uu____10479
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10474 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10490::uu____10491 ->
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
                                                   let uu____10514 =
                                                     let uu____10520 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10520) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10514 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10534 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10536 =
                                             match formals with
                                             | [] ->
                                                 let uu____10545 =
                                                   let uu____10546 =
                                                     let uu____10548 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_44  ->
                                                          Some _0_44)
                                                       uu____10548 in
                                                   push_free_var env1 lid
                                                     vname uu____10546 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10545)
                                             | uu____10551 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10556 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10556 in
                                                 let name_tok_corr =
                                                   let uu____10558 =
                                                     let uu____10562 =
                                                       let uu____10563 =
                                                         let uu____10569 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10569) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10563 in
                                                     (uu____10562,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10558 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10536 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10453 with
                                      | (decls2,env2) ->
                                          let uu____10593 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10598 =
                                              encode_term res_t1 env' in
                                            match uu____10598 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10606 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10606,
                                                  decls) in
                                          (match uu____10593 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10614 =
                                                   let uu____10618 =
                                                     let uu____10619 =
                                                       let uu____10625 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10625) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10619 in
                                                   (uu____10618,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10614 in
                                               let freshness =
                                                 let uu____10634 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10634
                                                 then
                                                   let uu____10637 =
                                                     let uu____10638 =
                                                       let uu____10644 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
                                                       let uu____10650 =
                                                         varops.next_id () in
                                                       (vname, uu____10644,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10650) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10638 in
                                                   let uu____10652 =
                                                     let uu____10654 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10654] in
                                                   uu____10637 :: uu____10652
                                                 else [] in
                                               let g =
                                                 let uu____10658 =
                                                   let uu____10660 =
                                                     let uu____10662 =
                                                       let uu____10664 =
                                                         let uu____10666 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10666 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10664 in
                                                     FStar_List.append decls3
                                                       uu____10662 in
                                                   FStar_List.append decls2
                                                     uu____10660 in
                                                 FStar_List.append decls11
                                                   uu____10658 in
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
          let uu____10688 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10688 with
          | None  ->
              let uu____10711 = encode_free_var env x t t_norm [] in
              (match uu____10711 with
               | (decls,env1) ->
                   let uu____10726 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10726 with
                    | (n1,x',uu____10745) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10757) -> ((n1, x1), [], env)
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
          let uu____10790 = encode_free_var env lid t tt quals in
          match uu____10790 with
          | (decls,env1) ->
              let uu____10801 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10801
              then
                let uu____10805 =
                  let uu____10807 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10807 in
                (uu____10805, env1)
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
             (fun uu____10835  ->
                fun lb  ->
                  match uu____10835 with
                  | (decls,env1) ->
                      let uu____10847 =
                        let uu____10851 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10851
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10847 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10865 = FStar_Syntax_Util.head_and_args t in
    match uu____10865 with
    | (hd1,args) ->
        let uu____10891 =
          let uu____10892 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10892.FStar_Syntax_Syntax.n in
        (match uu____10891 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10896,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10909 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10924  ->
      fun quals  ->
        match uu____10924 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10974 = FStar_Util.first_N nbinders formals in
              match uu____10974 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11016  ->
                         fun uu____11017  ->
                           match (uu____11016, uu____11017) with
                           | ((formal,uu____11027),(binder,uu____11029)) ->
                               let uu____11034 =
                                 let uu____11039 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11039) in
                               FStar_Syntax_Syntax.NT uu____11034) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11044 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11058  ->
                              match uu____11058 with
                              | (x,i) ->
                                  let uu____11065 =
                                    let uu___145_11066 = x in
                                    let uu____11067 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___145_11066.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___145_11066.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11067
                                    } in
                                  (uu____11065, i))) in
                    FStar_All.pipe_right uu____11044
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11079 =
                      let uu____11081 =
                        let uu____11082 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11082.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_45  -> Some _0_45)
                        uu____11081 in
                    let uu____11086 =
                      let uu____11087 = FStar_Syntax_Subst.compress body in
                      let uu____11088 =
                        let uu____11089 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11089 in
                      FStar_Syntax_Syntax.extend_app_n uu____11087
                        uu____11088 in
                    uu____11086 uu____11079 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11131 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11131
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___146_11132 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___146_11132.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___146_11132.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___146_11132.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___146_11132.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___146_11132.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___146_11132.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___146_11132.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___146_11132.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___146_11132.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___146_11132.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___146_11132.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___146_11132.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___146_11132.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___146_11132.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___146_11132.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___146_11132.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___146_11132.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___146_11132.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___146_11132.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___146_11132.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___146_11132.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___146_11132.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___146_11132.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___146_11132.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___146_11132.FStar_TypeChecker_Env.synth)
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
                                   let uu____11267 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11267
                                   then
                                     let uu____11290 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11290 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11338  ->
                                                   fun uu____11339  ->
                                                     match (uu____11338,
                                                             uu____11339)
                                                     with
                                                     | ((x,uu____11349),
                                                        (b,uu____11351)) ->
                                                         let uu____11356 =
                                                           let uu____11361 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11361) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11356)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11363 =
                                            let uu____11374 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11374) in
                                          (uu____11363, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11414 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11414 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11466) ->
                              let uu____11471 =
                                let uu____11482 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____11482 in
                              (uu____11471, true)
                          | uu____11515 when Prims.op_Negation norm1 ->
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
                          | uu____11517 ->
                              let uu____11518 =
                                let uu____11519 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11520 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11519
                                  uu____11520 in
                              failwith uu____11518)
                     | uu____11533 ->
                         let uu____11534 =
                           let uu____11535 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11535.FStar_Syntax_Syntax.n in
                         (match uu____11534 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11562 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11562 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11580 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11580 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11628 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11656 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11656
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11663 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11704  ->
                            fun lb  ->
                              match uu____11704 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11755 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11755
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11758 =
                                      let uu____11766 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11766
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11758 with
                                    | (tok,decl,env2) ->
                                        let uu____11791 =
                                          let uu____11798 =
                                            let uu____11804 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11804, tok) in
                                          uu____11798 :: toks in
                                        (uu____11791, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11663 with
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
                        | uu____11906 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11911 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11911 vars)
                            else
                              (let uu____11913 =
                                 let uu____11917 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11917) in
                               FStar_SMTEncoding_Util.mkApp uu____11913) in
                      let uu____11922 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___115_11924  ->
                                 match uu___115_11924 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11925 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11928 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11928))) in
                      if uu____11922
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11948;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11950;
                                FStar_Syntax_Syntax.lbeff = uu____11951;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11992 =
                                 let uu____11996 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11996 with
                                 | (tcenv',uu____12007,e_t) ->
                                     let uu____12011 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12018 -> failwith "Impossible" in
                                     (match uu____12011 with
                                      | (e1,t_norm1) ->
                                          ((let uu___149_12027 = env1 in
                                            {
                                              bindings =
                                                (uu___149_12027.bindings);
                                              depth = (uu___149_12027.depth);
                                              tcenv = tcenv';
                                              warn = (uu___149_12027.warn);
                                              cache = (uu___149_12027.cache);
                                              nolabels =
                                                (uu___149_12027.nolabels);
                                              use_zfuel_name =
                                                (uu___149_12027.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___149_12027.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___149_12027.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11992 with
                                | (env',e1,t_norm1) ->
                                    let uu____12034 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____12034 with
                                     | ((binders,body,uu____12046,uu____12047),curry)
                                         ->
                                         ((let uu____12054 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____12054
                                           then
                                             let uu____12055 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12056 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12055 uu____12056
                                           else ());
                                          (let uu____12058 =
                                             encode_binders None binders env' in
                                           match uu____12058 with
                                           | (vars,guards,env'1,binder_decls,uu____12074)
                                               ->
                                               let body1 =
                                                 let uu____12082 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12082
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12085 =
                                                 let uu____12090 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12090
                                                 then
                                                   let uu____12096 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12097 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12096, uu____12097)
                                                 else
                                                   (let uu____12103 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12103)) in
                                               (match uu____12085 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12117 =
                                                        let uu____12121 =
                                                          let uu____12122 =
                                                            let uu____12128 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12128) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12122 in
                                                        let uu____12134 =
                                                          let uu____12136 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12136 in
                                                        (uu____12121,
                                                          uu____12134,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12117 in
                                                    let uu____12138 =
                                                      let uu____12140 =
                                                        let uu____12142 =
                                                          let uu____12144 =
                                                            let uu____12146 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12146 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12144 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12142 in
                                                      FStar_List.append
                                                        decls1 uu____12140 in
                                                    (uu____12138, env1))))))
                           | uu____12149 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12168 = varops.fresh "fuel" in
                             (uu____12168, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12171 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12210  ->
                                     fun uu____12211  ->
                                       match (uu____12210, uu____12211) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12293 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12293 in
                                           let gtok =
                                             let uu____12295 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12295 in
                                           let env3 =
                                             let uu____12297 =
                                               let uu____12299 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_46  -> Some _0_46)
                                                 uu____12299 in
                                             push_free_var env2 flid gtok
                                               uu____12297 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12171 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12385
                                 t_norm uu____12387 =
                                 match (uu____12385, uu____12387) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12414;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12415;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12432 =
                                       let uu____12436 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12436 with
                                       | (tcenv',uu____12451,e_t) ->
                                           let uu____12455 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12462 ->
                                                 failwith "Impossible" in
                                           (match uu____12455 with
                                            | (e1,t_norm1) ->
                                                ((let uu___150_12471 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___150_12471.bindings);
                                                    depth =
                                                      (uu___150_12471.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___150_12471.warn);
                                                    cache =
                                                      (uu___150_12471.cache);
                                                    nolabels =
                                                      (uu___150_12471.nolabels);
                                                    use_zfuel_name =
                                                      (uu___150_12471.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___150_12471.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___150_12471.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12432 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12481 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12481
                                            then
                                              let uu____12482 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12483 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12484 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12482 uu____12483
                                                uu____12484
                                            else ());
                                           (let uu____12486 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12486 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12508 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12508
                                                  then
                                                    let uu____12509 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12510 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12511 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12512 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12509 uu____12510
                                                      uu____12511 uu____12512
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12516 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12516 with
                                                  | (vars,guards,env'1,binder_decls,uu____12534)
                                                      ->
                                                      let decl_g =
                                                        let uu____12542 =
                                                          let uu____12548 =
                                                            let uu____12550 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12550 in
                                                          (g, uu____12548,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12542 in
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
                                                        let uu____12565 =
                                                          let uu____12569 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12569) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12565 in
                                                      let gsapp =
                                                        let uu____12575 =
                                                          let uu____12579 =
                                                            let uu____12581 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12581 ::
                                                              vars_tm in
                                                          (g, uu____12579) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12575 in
                                                      let gmax =
                                                        let uu____12585 =
                                                          let uu____12589 =
                                                            let uu____12591 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12591 ::
                                                              vars_tm in
                                                          (g, uu____12589) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12585 in
                                                      let body1 =
                                                        let uu____12595 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12595
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12597 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12597 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12608
                                                               =
                                                               let uu____12612
                                                                 =
                                                                 let uu____12613
                                                                   =
                                                                   let uu____12621
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
                                                                    uu____12621) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12613 in
                                                               let uu____12632
                                                                 =
                                                                 let uu____12634
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12634 in
                                                               (uu____12612,
                                                                 uu____12632,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12608 in
                                                           let eqn_f =
                                                             let uu____12637
                                                               =
                                                               let uu____12641
                                                                 =
                                                                 let uu____12642
                                                                   =
                                                                   let uu____12648
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12648) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12642 in
                                                               (uu____12641,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12637 in
                                                           let eqn_g' =
                                                             let uu____12656
                                                               =
                                                               let uu____12660
                                                                 =
                                                                 let uu____12661
                                                                   =
                                                                   let uu____12667
                                                                    =
                                                                    let uu____12668
                                                                    =
                                                                    let uu____12671
                                                                    =
                                                                    let uu____12672
                                                                    =
                                                                    let uu____12676
                                                                    =
                                                                    let uu____12678
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12678
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12676) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12672 in
                                                                    (gsapp,
                                                                    uu____12671) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12668 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12667) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12661 in
                                                               (uu____12660,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12656 in
                                                           let uu____12690 =
                                                             let uu____12695
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12695
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12712)
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
                                                                    let uu____12727
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12727
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12730
                                                                    =
                                                                    let uu____12734
                                                                    =
                                                                    let uu____12735
                                                                    =
                                                                    let uu____12741
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12741) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12735 in
                                                                    (uu____12734,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12730 in
                                                                 let uu____12752
                                                                   =
                                                                   let uu____12756
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12756
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12764
                                                                    =
                                                                    let uu____12766
                                                                    =
                                                                    let uu____12767
                                                                    =
                                                                    let uu____12771
                                                                    =
                                                                    let uu____12772
                                                                    =
                                                                    let uu____12778
                                                                    =
                                                                    let uu____12779
                                                                    =
                                                                    let uu____12782
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12782,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12779 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12778) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12772 in
                                                                    (uu____12771,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12767 in
                                                                    [uu____12766] in
                                                                    (d3,
                                                                    uu____12764) in
                                                                 (match uu____12752
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12690
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
                               let uu____12817 =
                                 let uu____12824 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12860  ->
                                      fun uu____12861  ->
                                        match (uu____12860, uu____12861) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12947 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12947 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12824 in
                               (match uu____12817 with
                                | (decls2,eqns,env01) ->
                                    let uu____12987 =
                                      let isDeclFun uu___116_12995 =
                                        match uu___116_12995 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12996 -> true
                                        | uu____13002 -> false in
                                      let uu____13003 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____13003
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12987 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____13030 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____13030
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
        let uu____13063 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13063 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____13066 = encode_sigelt' env se in
      match uu____13066 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13076 =
                  let uu____13077 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13077 in
                [uu____13076]
            | uu____13078 ->
                let uu____13079 =
                  let uu____13081 =
                    let uu____13082 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13082 in
                  uu____13081 :: g in
                let uu____13083 =
                  let uu____13085 =
                    let uu____13086 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13086 in
                  [uu____13085] in
                FStar_List.append uu____13079 uu____13083 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____13096 =
          let uu____13097 = FStar_Syntax_Subst.compress t in
          uu____13097.FStar_Syntax_Syntax.n in
        match uu____13096 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____13101)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____13104 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13107 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13110 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13112 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13114 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13122 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13125 =
            let uu____13126 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13126 Prims.op_Negation in
          if uu____13125
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13146 ->
                   let uu____13147 =
                     let uu____13150 =
                       let uu____13151 =
                         let uu____13166 =
                           FStar_All.pipe_left (fun _0_47  -> Some _0_47)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13166) in
                       FStar_Syntax_Syntax.Tm_abs uu____13151 in
                     FStar_Syntax_Syntax.mk uu____13150 in
                   uu____13147 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13219 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13219 with
               | (aname,atok,env2) ->
                   let uu____13229 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13229 with
                    | (formals,uu____13239) ->
                        let uu____13246 =
                          let uu____13249 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13249 env2 in
                        (match uu____13246 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13257 =
                                 let uu____13258 =
                                   let uu____13264 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13272  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13264,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13258 in
                               [uu____13257;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13279 =
                               let aux uu____13308 uu____13309 =
                                 match (uu____13308, uu____13309) with
                                 | ((bv,uu____13336),(env3,acc_sorts,acc)) ->
                                     let uu____13357 = gen_term_var env3 bv in
                                     (match uu____13357 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13279 with
                              | (uu____13395,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13409 =
                                      let uu____13413 =
                                        let uu____13414 =
                                          let uu____13420 =
                                            let uu____13421 =
                                              let uu____13424 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13424) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13421 in
                                          ([[app]], xs_sorts, uu____13420) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13414 in
                                      (uu____13413, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13409 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13436 =
                                      let uu____13440 =
                                        let uu____13441 =
                                          let uu____13447 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13447) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13441 in
                                      (uu____13440,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13436 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13457 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13457 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13473,uu____13474)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13475 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13475 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13486,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13491 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___117_13493  ->
                      match uu___117_13493 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13494 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13497 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13498 -> false)) in
            Prims.op_Negation uu____13491 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13504 = encode_top_level_val env fv t quals in
             match uu____13504 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13516 =
                   let uu____13518 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13518 in
                 (uu____13516, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13523 = encode_formula f env in
          (match uu____13523 with
           | (f1,decls) ->
               let g =
                 let uu____13532 =
                   let uu____13533 =
                     let uu____13537 =
                       let uu____13539 =
                         let uu____13540 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13540 in
                       Some uu____13539 in
                     let uu____13541 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13537, uu____13541) in
                   FStar_SMTEncoding_Util.mkAssume uu____13533 in
                 [uu____13532] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13545,attrs) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right attrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let uu____13553 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13560 =
                       let uu____13565 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13565.FStar_Syntax_Syntax.fv_name in
                     uu____13560.FStar_Syntax_Syntax.v in
                   let uu____13569 =
                     let uu____13570 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13570 in
                   if uu____13569
                   then
                     let val_decl =
                       let uu___151_13585 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___151_13585.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___151_13585.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13589 = encode_sigelt' env1 val_decl in
                     match uu____13589 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____13553 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13606,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13608;
                          FStar_Syntax_Syntax.lbtyp = uu____13609;
                          FStar_Syntax_Syntax.lbeff = uu____13610;
                          FStar_Syntax_Syntax.lbdef = uu____13611;_}::[]),uu____13612,uu____13613)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13627 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13627 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13650 =
                   let uu____13652 =
                     let uu____13653 =
                       let uu____13657 =
                         let uu____13658 =
                           let uu____13664 =
                             let uu____13665 =
                               let uu____13668 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13668) in
                             FStar_SMTEncoding_Util.mkEq uu____13665 in
                           ([[b2t_x]], [xx], uu____13664) in
                         FStar_SMTEncoding_Util.mkForall uu____13658 in
                       (uu____13657, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13653 in
                   [uu____13652] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13650 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13685,uu____13686,uu____13687)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___118_13693  ->
                  match uu___118_13693 with
                  | FStar_Syntax_Syntax.Discriminator uu____13694 -> true
                  | uu____13695 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13697,lids,uu____13699) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13706 =
                     let uu____13707 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13707.FStar_Ident.idText in
                   uu____13706 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___119_13709  ->
                     match uu___119_13709 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13710 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13713,uu____13714)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___120_13724  ->
                  match uu___120_13724 with
                  | FStar_Syntax_Syntax.Projector uu____13725 -> true
                  | uu____13728 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13735 = try_lookup_free_var env l in
          (match uu____13735 with
           | Some uu____13739 -> ([], env)
           | None  ->
               let se1 =
                 let uu___152_13742 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___152_13742.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___152_13742.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13748,uu____13749) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13761) ->
          let uu____13766 = encode_sigelts env ses in
          (match uu____13766 with
           | (g,env1) ->
               let uu____13776 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___121_13786  ->
                         match uu___121_13786 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13787;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13788;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13789;_}
                             -> false
                         | uu____13791 -> true)) in
               (match uu____13776 with
                | (g',inversions) ->
                    let uu____13800 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___122_13810  ->
                              match uu___122_13810 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13811 ->
                                  true
                              | uu____13817 -> false)) in
                    (match uu____13800 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13828,tps,k,uu____13831,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___123_13841  ->
                    match uu___123_13841 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13842 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13849 = c in
              match uu____13849 with
              | (name,args,uu____13853,uu____13854,uu____13855) ->
                  let uu____13858 =
                    let uu____13859 =
                      let uu____13865 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13872  ->
                                match uu____13872 with
                                | (uu____13876,sort,uu____13878) -> sort)) in
                      (name, uu____13865, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13859 in
                  [uu____13858]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13896 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13899 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13899 FStar_Option.isNone)) in
            if uu____13896
            then []
            else
              (let uu____13916 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13916 with
               | (xxsym,xx) ->
                   let uu____13922 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13933  ->
                             fun l  ->
                               match uu____13933 with
                               | (out,decls) ->
                                   let uu____13945 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13945 with
                                    | (uu____13951,data_t) ->
                                        let uu____13953 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13953 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13982 =
                                                 let uu____13983 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13983.FStar_Syntax_Syntax.n in
                                               match uu____13982 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13991,indices) ->
                                                   indices
                                               | uu____14007 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____14019  ->
                                                         match uu____14019
                                                         with
                                                         | (x,uu____14023) ->
                                                             let uu____14024
                                                               =
                                                               let uu____14025
                                                                 =
                                                                 let uu____14029
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____14029,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14025 in
                                                             push_term_var
                                                               env1 x
                                                               uu____14024)
                                                    env) in
                                             let uu____14031 =
                                               encode_args indices env1 in
                                             (match uu____14031 with
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
                                                      let uu____14055 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14063
                                                                 =
                                                                 let uu____14066
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____14066,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14063)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____14055
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____14068 =
                                                      let uu____14069 =
                                                        let uu____14072 =
                                                          let uu____14073 =
                                                            let uu____14076 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____14076,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14073 in
                                                        (out, uu____14072) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14069 in
                                                    (uu____14068,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13922 with
                    | (data_ax,decls) ->
                        let uu____14084 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14084 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14098 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14098 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14101 =
                                 let uu____14105 =
                                   let uu____14106 =
                                     let uu____14112 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14120 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14112,
                                       uu____14120) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14106 in
                                 let uu____14128 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14105, (Some "inversion axiom"),
                                   uu____14128) in
                               FStar_SMTEncoding_Util.mkAssume uu____14101 in
                             let pattern_guarded_inversion =
                               let uu____14132 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14132
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14143 =
                                   let uu____14144 =
                                     let uu____14148 =
                                       let uu____14149 =
                                         let uu____14155 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14163 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14155, uu____14163) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14149 in
                                     let uu____14171 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14148, (Some "inversion axiom"),
                                       uu____14171) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14144 in
                                 [uu____14143]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14174 =
            let uu____14182 =
              let uu____14183 = FStar_Syntax_Subst.compress k in
              uu____14183.FStar_Syntax_Syntax.n in
            match uu____14182 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14212 -> (tps, k) in
          (match uu____14174 with
           | (formals,res) ->
               let uu____14227 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14227 with
                | (formals1,res1) ->
                    let uu____14234 = encode_binders None formals1 env in
                    (match uu____14234 with
                     | (vars,guards,env',binder_decls,uu____14249) ->
                         let uu____14256 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14256 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14269 =
                                  let uu____14273 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14273) in
                                FStar_SMTEncoding_Util.mkApp uu____14269 in
                              let uu____14278 =
                                let tname_decl =
                                  let uu____14284 =
                                    let uu____14285 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14300  ->
                                              match uu____14300 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14308 = varops.next_id () in
                                    (tname, uu____14285,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14308, false) in
                                  constructor_or_logic_type_decl uu____14284 in
                                let uu____14313 =
                                  match vars with
                                  | [] ->
                                      let uu____14320 =
                                        let uu____14321 =
                                          let uu____14323 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_48  -> Some _0_48)
                                            uu____14323 in
                                        push_free_var env1 t tname
                                          uu____14321 in
                                      ([], uu____14320)
                                  | uu____14327 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14333 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14333 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14342 =
                                          let uu____14346 =
                                            let uu____14347 =
                                              let uu____14355 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14355) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14347 in
                                          (uu____14346,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14342 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14313 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14278 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14378 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14378 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14395 =
                                               let uu____14396 =
                                                 let uu____14400 =
                                                   let uu____14401 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14401 in
                                                 (uu____14400,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14396 in
                                             [uu____14395]
                                           else [] in
                                         let uu____14404 =
                                           let uu____14406 =
                                             let uu____14408 =
                                               let uu____14409 =
                                                 let uu____14413 =
                                                   let uu____14414 =
                                                     let uu____14420 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14420) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14414 in
                                                 (uu____14413, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14409 in
                                             [uu____14408] in
                                           FStar_List.append karr uu____14406 in
                                         FStar_List.append decls1 uu____14404 in
                                   let aux =
                                     let uu____14429 =
                                       let uu____14431 =
                                         inversion_axioms tapp vars in
                                       let uu____14433 =
                                         let uu____14435 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14435] in
                                       FStar_List.append uu____14431
                                         uu____14433 in
                                     FStar_List.append kindingAx uu____14429 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14440,uu____14441,uu____14442,uu____14443,uu____14444)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14449,t,uu____14451,n_tps,uu____14453) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14458 = new_term_constant_and_tok_from_lid env d in
          (match uu____14458 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14469 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14469 with
                | (formals,t_res) ->
                    let uu____14491 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14491 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14500 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14500 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14538 =
                                            mk_term_projector_name d x in
                                          (uu____14538,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14540 =
                                  let uu____14550 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14550, true) in
                                FStar_All.pipe_right uu____14540
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
                              let uu____14572 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14572 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14580::uu____14581 ->
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
                                         let uu____14606 =
                                           let uu____14612 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14612) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14606
                                     | uu____14625 -> tok_typing in
                                   let uu____14630 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14630 with
                                    | (vars',guards',env'',decls_formals,uu____14645)
                                        ->
                                        let uu____14652 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14652 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14671 ->
                                                   let uu____14675 =
                                                     let uu____14676 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14676 in
                                                   [uu____14675] in
                                             let encode_elim uu____14683 =
                                               let uu____14684 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14684 with
                                               | (head1,args) ->
                                                   let uu____14713 =
                                                     let uu____14714 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14714.FStar_Syntax_Syntax.n in
                                                   (match uu____14713 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____14721;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14722;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14723;_},uu____14724)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14734 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14734
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
                                                                 | uu____14760
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14768
                                                                    =
                                                                    let uu____14769
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14769 in
                                                                    if
                                                                    uu____14768
                                                                    then
                                                                    let uu____14776
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14776]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14778
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14791
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14791
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14813
                                                                    =
                                                                    let uu____14817
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14817 in
                                                                    (match uu____14813
                                                                    with
                                                                    | 
                                                                    (uu____14824,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14830
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14830
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14832
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14832
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
                                                             (match uu____14778
                                                              with
                                                              | (uu____14840,arg_vars,elim_eqns_or_guards,uu____14843)
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
                                                                    let uu____14862
                                                                    =
                                                                    let uu____14866
                                                                    =
                                                                    let uu____14867
                                                                    =
                                                                    let uu____14873
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14879
                                                                    =
                                                                    let uu____14880
                                                                    =
                                                                    let uu____14883
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14883) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14880 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14873,
                                                                    uu____14879) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14867 in
                                                                    (uu____14866,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14862 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14896
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14896,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14898
                                                                    =
                                                                    let uu____14902
                                                                    =
                                                                    let uu____14903
                                                                    =
                                                                    let uu____14909
                                                                    =
                                                                    let uu____14912
                                                                    =
                                                                    let uu____14914
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14914] in
                                                                    [uu____14912] in
                                                                    let uu____14917
                                                                    =
                                                                    let uu____14918
                                                                    =
                                                                    let uu____14921
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14922
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14921,
                                                                    uu____14922) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14918 in
                                                                    (uu____14909,
                                                                    [x],
                                                                    uu____14917) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14903 in
                                                                    let uu____14932
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14902,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14932) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14898
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14937
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
                                                                    (let uu____14952
                                                                    =
                                                                    let uu____14953
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14953
                                                                    dapp1 in
                                                                    [uu____14952]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14937
                                                                    FStar_List.flatten in
                                                                    let uu____14957
                                                                    =
                                                                    let uu____14961
                                                                    =
                                                                    let uu____14962
                                                                    =
                                                                    let uu____14968
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14974
                                                                    =
                                                                    let uu____14975
                                                                    =
                                                                    let uu____14978
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14978) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14975 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14968,
                                                                    uu____14974) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14962 in
                                                                    (uu____14961,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14957) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14994 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14994
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
                                                                 | uu____15020
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15028
                                                                    =
                                                                    let uu____15029
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15029 in
                                                                    if
                                                                    uu____15028
                                                                    then
                                                                    let uu____15036
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15036]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15038
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15051
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15051
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15073
                                                                    =
                                                                    let uu____15077
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15077 in
                                                                    (match uu____15073
                                                                    with
                                                                    | 
                                                                    (uu____15084,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15090
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15090
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15092
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15092
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
                                                             (match uu____15038
                                                              with
                                                              | (uu____15100,arg_vars,elim_eqns_or_guards,uu____15103)
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
                                                                    let uu____15122
                                                                    =
                                                                    let uu____15126
                                                                    =
                                                                    let uu____15127
                                                                    =
                                                                    let uu____15133
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15139
                                                                    =
                                                                    let uu____15140
                                                                    =
                                                                    let uu____15143
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15143) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15140 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15133,
                                                                    uu____15139) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15127 in
                                                                    (uu____15126,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15122 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15156
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15156,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15158
                                                                    =
                                                                    let uu____15162
                                                                    =
                                                                    let uu____15163
                                                                    =
                                                                    let uu____15169
                                                                    =
                                                                    let uu____15172
                                                                    =
                                                                    let uu____15174
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15174] in
                                                                    [uu____15172] in
                                                                    let uu____15177
                                                                    =
                                                                    let uu____15178
                                                                    =
                                                                    let uu____15181
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15182
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15181,
                                                                    uu____15182) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15178 in
                                                                    (uu____15169,
                                                                    [x],
                                                                    uu____15177) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15163 in
                                                                    let uu____15192
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15162,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15192) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15158
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15197
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
                                                                    (let uu____15212
                                                                    =
                                                                    let uu____15213
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15213
                                                                    dapp1 in
                                                                    [uu____15212]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15197
                                                                    FStar_List.flatten in
                                                                    let uu____15217
                                                                    =
                                                                    let uu____15221
                                                                    =
                                                                    let uu____15222
                                                                    =
                                                                    let uu____15228
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15234
                                                                    =
                                                                    let uu____15235
                                                                    =
                                                                    let uu____15238
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15238) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15235 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15228,
                                                                    uu____15234) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15222 in
                                                                    (uu____15221,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15217) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15248 ->
                                                        ((let uu____15250 =
                                                            let uu____15251 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15252 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15251
                                                              uu____15252 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15250);
                                                         ([], []))) in
                                             let uu____15255 = encode_elim () in
                                             (match uu____15255 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15267 =
                                                      let uu____15269 =
                                                        let uu____15271 =
                                                          let uu____15273 =
                                                            let uu____15275 =
                                                              let uu____15276
                                                                =
                                                                let uu____15282
                                                                  =
                                                                  let uu____15284
                                                                    =
                                                                    let uu____15285
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15285 in
                                                                  Some
                                                                    uu____15284 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15282) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15276 in
                                                            [uu____15275] in
                                                          let uu____15288 =
                                                            let uu____15290 =
                                                              let uu____15292
                                                                =
                                                                let uu____15294
                                                                  =
                                                                  let uu____15296
                                                                    =
                                                                    let uu____15298
                                                                    =
                                                                    let uu____15300
                                                                    =
                                                                    let uu____15301
                                                                    =
                                                                    let uu____15305
                                                                    =
                                                                    let uu____15306
                                                                    =
                                                                    let uu____15312
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15312) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15306 in
                                                                    (uu____15305,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15301 in
                                                                    let uu____15319
                                                                    =
                                                                    let uu____15321
                                                                    =
                                                                    let uu____15322
                                                                    =
                                                                    let uu____15326
                                                                    =
                                                                    let uu____15327
                                                                    =
                                                                    let uu____15333
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____15339
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15333,
                                                                    uu____15339) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15327 in
                                                                    (uu____15326,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15322 in
                                                                    [uu____15321] in
                                                                    uu____15300
                                                                    ::
                                                                    uu____15319 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15298 in
                                                                  FStar_List.append
                                                                    uu____15296
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15294 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15292 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15290 in
                                                          FStar_List.append
                                                            uu____15273
                                                            uu____15288 in
                                                        FStar_List.append
                                                          decls3 uu____15271 in
                                                      FStar_List.append
                                                        decls2 uu____15269 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15267 in
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
           (fun uu____15360  ->
              fun se  ->
                match uu____15360 with
                | (g,env1) ->
                    let uu____15372 = encode_sigelt env1 se in
                    (match uu____15372 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15408 =
        match uu____15408 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15426 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____15431 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15431
                   then
                     let uu____15432 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15433 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15434 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15432 uu____15433 uu____15434
                   else ());
                  (let uu____15436 = encode_term t1 env1 in
                   match uu____15436 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15446 =
                         let uu____15450 =
                           let uu____15451 =
                             let uu____15452 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15452
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15451 in
                         new_term_constant_from_string env1 x uu____15450 in
                       (match uu____15446 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15463 = FStar_Options.log_queries () in
                              if uu____15463
                              then
                                let uu____15465 =
                                  let uu____15466 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15467 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15468 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15466 uu____15467 uu____15468 in
                                Some uu____15465
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15479,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15488 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15488 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15501,se,uu____15503) ->
                 let uu____15506 = encode_sigelt env1 se in
                 (match uu____15506 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15516,se) ->
                 let uu____15520 = encode_sigelt env1 se in
                 (match uu____15520 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15530 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15530 with | (uu____15542,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15587  ->
            match uu____15587 with
            | (l,uu____15594,uu____15595) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15616  ->
            match uu____15616 with
            | (l,uu____15624,uu____15625) ->
                let uu____15630 =
                  FStar_All.pipe_left
                    (fun _0_49  -> FStar_SMTEncoding_Term.Echo _0_49) (
                    fst l) in
                let uu____15631 =
                  let uu____15633 =
                    let uu____15634 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15634 in
                  [uu____15633] in
                uu____15630 :: uu____15631)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15645 =
      let uu____15647 =
        let uu____15648 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15650 =
          let uu____15651 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15651 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15648;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15650
        } in
      [uu____15647] in
    FStar_ST.write last_env uu____15645
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15661 = FStar_ST.read last_env in
      match uu____15661 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15667 ->
          let uu___153_15669 = e in
          let uu____15670 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___153_15669.bindings);
            depth = (uu___153_15669.depth);
            tcenv;
            warn = (uu___153_15669.warn);
            cache = (uu___153_15669.cache);
            nolabels = (uu___153_15669.nolabels);
            use_zfuel_name = (uu___153_15669.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___153_15669.encode_non_total_function_typ);
            current_module_name = uu____15670
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15674 = FStar_ST.read last_env in
    match uu____15674 with
    | [] -> failwith "Empty env stack"
    | uu____15679::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15687  ->
    let uu____15688 = FStar_ST.read last_env in
    match uu____15688 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___154_15699 = hd1 in
          {
            bindings = (uu___154_15699.bindings);
            depth = (uu___154_15699.depth);
            tcenv = (uu___154_15699.tcenv);
            warn = (uu___154_15699.warn);
            cache = refs;
            nolabels = (uu___154_15699.nolabels);
            use_zfuel_name = (uu___154_15699.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15699.encode_non_total_function_typ);
            current_module_name = (uu___154_15699.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15705  ->
    let uu____15706 = FStar_ST.read last_env in
    match uu____15706 with
    | [] -> failwith "Popping an empty stack"
    | uu____15711::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15719  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15722  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15725  ->
    let uu____15726 = FStar_ST.read last_env in
    match uu____15726 with
    | hd1::uu____15732::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15738 -> failwith "Impossible"
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
        | (uu____15787::uu____15788,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___155_15792 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___155_15792.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___155_15792.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___155_15792.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15793 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15804 =
        let uu____15806 =
          let uu____15807 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15807 in
        let uu____15808 = open_fact_db_tags env in uu____15806 :: uu____15808 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15804
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
      let uu____15823 = encode_sigelt env se in
      match uu____15823 with
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
        let uu____15848 = FStar_Options.log_queries () in
        if uu____15848
        then
          let uu____15850 =
            let uu____15851 =
              let uu____15852 =
                let uu____15853 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15853 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15852 in
            FStar_SMTEncoding_Term.Caption uu____15851 in
          uu____15850 :: decls
        else decls in
      let env =
        let uu____15860 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15860 tcenv in
      let uu____15861 = encode_top_level_facts env se in
      match uu____15861 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15870 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15870))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15881 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15881
       then
         let uu____15882 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15882
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15905  ->
                 fun se  ->
                   match uu____15905 with
                   | (g,env2) ->
                       let uu____15917 = encode_top_level_facts env2 se in
                       (match uu____15917 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15930 =
         encode_signature
           (let uu___156_15934 = env in
            {
              bindings = (uu___156_15934.bindings);
              depth = (uu___156_15934.depth);
              tcenv = (uu___156_15934.tcenv);
              warn = false;
              cache = (uu___156_15934.cache);
              nolabels = (uu___156_15934.nolabels);
              use_zfuel_name = (uu___156_15934.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_15934.encode_non_total_function_typ);
              current_module_name = (uu___156_15934.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15930 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15946 = FStar_Options.log_queries () in
             if uu____15946
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___157_15951 = env1 in
               {
                 bindings = (uu___157_15951.bindings);
                 depth = (uu___157_15951.depth);
                 tcenv = (uu___157_15951.tcenv);
                 warn = true;
                 cache = (uu___157_15951.cache);
                 nolabels = (uu___157_15951.nolabels);
                 use_zfuel_name = (uu___157_15951.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___157_15951.encode_non_total_function_typ);
                 current_module_name = (uu___157_15951.current_module_name)
               });
            (let uu____15953 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15953
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
        (let uu____15988 =
           let uu____15989 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15989.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15988);
        (let env =
           let uu____15991 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15991 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15998 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16019 = aux rest in
                 (match uu____16019 with
                  | (out,rest1) ->
                      let t =
                        let uu____16037 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____16037 with
                        | Some uu____16041 ->
                            let uu____16042 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16042
                              x.FStar_Syntax_Syntax.sort
                        | uu____16043 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____16046 =
                        let uu____16048 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___158_16049 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_16049.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_16049.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16048 :: out in
                      (uu____16046, rest1))
             | uu____16052 -> ([], bindings1) in
           let uu____16056 = aux bindings in
           match uu____16056 with
           | (closing,bindings1) ->
               let uu____16070 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16070, bindings1) in
         match uu____15998 with
         | (q1,bindings1) ->
             let uu____16083 =
               let uu____16086 =
                 FStar_List.filter
                   (fun uu___124_16088  ->
                      match uu___124_16088 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16089 ->
                          false
                      | uu____16093 -> true) bindings1 in
               encode_env_bindings env uu____16086 in
             (match uu____16083 with
              | (env_decls,env1) ->
                  ((let uu____16104 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16104
                    then
                      let uu____16105 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16105
                    else ());
                   (let uu____16107 = encode_formula q1 env1 in
                    match uu____16107 with
                    | (phi,qdecls) ->
                        let uu____16119 =
                          let uu____16122 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16122 phi in
                        (match uu____16119 with
                         | (labels,phi1) ->
                             let uu____16132 = encode_labels labels in
                             (match uu____16132 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____16153 =
                                      let uu____16157 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16158 =
                                        varops.mk_unique "@query" in
                                      (uu____16157, (Some "query"),
                                        uu____16158) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16153 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16171 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16171 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16173 = encode_formula q env in
       match uu____16173 with
       | (f,uu____16177) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16179) -> true
             | uu____16182 -> false)))