open Prims
let add_fuel x tl1 =
  let uu____16 = FStar_Options.unthrottle_inductives () in
  if uu____16 then tl1 else x :: tl1
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___111_74  ->
       match uu___111_74 with
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
        let uu___135_140 = a in
        let uu____141 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___135_140.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___135_140.FStar_Syntax_Syntax.sort)
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
    let uu___136_780 = x in
    let uu____781 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____781;
      FStar_Syntax_Syntax.index = (uu___136_780.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___136_780.FStar_Syntax_Syntax.sort)
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
type env_t =
  {
  bindings: binding Prims.list;
  depth: Prims.int;
  tcenv: FStar_TypeChecker_Env.env;
  warn: Prims.bool;
  cache:
    (Prims.string* FStar_SMTEncoding_Term.sort Prims.list*
      FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap;
  nolabels: Prims.bool;
  use_zfuel_name: Prims.bool;
  encode_non_total_function_typ: Prims.bool;
  current_module_name: Prims.string;}
let print_env: env_t -> Prims.string =
  fun e  ->
    let uu____952 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___112_956  ->
              match uu___112_956 with
              | Binding_var (x,uu____958) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____960,uu____961,uu____962) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____952 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option
  =
  fun env  ->
    fun t  ->
      let uu____995 = FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____995
      then
        let uu____997 = FStar_Syntax_Print.term_to_string t in Some uu____997
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1008 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1008)
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
        (let uu___137_1020 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___137_1020.tcenv);
           warn = (uu___137_1020.warn);
           cache = (uu___137_1020.cache);
           nolabels = (uu___137_1020.nolabels);
           use_zfuel_name = (uu___137_1020.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___137_1020.encode_non_total_function_typ);
           current_module_name = (uu___137_1020.current_module_name)
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
        (let uu___138_1033 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___138_1033.depth);
           tcenv = (uu___138_1033.tcenv);
           warn = (uu___138_1033.warn);
           cache = (uu___138_1033.cache);
           nolabels = (uu___138_1033.nolabels);
           use_zfuel_name = (uu___138_1033.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___138_1033.encode_non_total_function_typ);
           current_module_name = (uu___138_1033.current_module_name)
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
          (let uu___139_1049 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___139_1049.depth);
             tcenv = (uu___139_1049.tcenv);
             warn = (uu___139_1049.warn);
             cache = (uu___139_1049.cache);
             nolabels = (uu___139_1049.nolabels);
             use_zfuel_name = (uu___139_1049.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___139_1049.encode_non_total_function_typ);
             current_module_name = (uu___139_1049.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___140_1059 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___140_1059.depth);
          tcenv = (uu___140_1059.tcenv);
          warn = (uu___140_1059.warn);
          cache = (uu___140_1059.cache);
          nolabels = (uu___140_1059.nolabels);
          use_zfuel_name = (uu___140_1059.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___140_1059.encode_non_total_function_typ);
          current_module_name = (uu___140_1059.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___113_1075  ->
             match uu___113_1075 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1083 -> None) in
      let uu____1086 = aux a in
      match uu____1086 with
      | None  ->
          let a2 = unmangle a in
          let uu____1093 = aux a2 in
          (match uu____1093 with
           | None  ->
               let uu____1099 =
                 let uu____1100 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1101 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1100 uu____1101 in
               failwith uu____1099
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1121 =
        let uu___141_1122 = env in
        let uu____1123 =
          let uu____1125 =
            let uu____1126 =
              let uu____1133 =
                let uu____1135 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1135 in
              (x, fname, uu____1133, None) in
            Binding_fvar uu____1126 in
          uu____1125 :: (env.bindings) in
        {
          bindings = uu____1123;
          depth = (uu___141_1122.depth);
          tcenv = (uu___141_1122.tcenv);
          warn = (uu___141_1122.warn);
          cache = (uu___141_1122.cache);
          nolabels = (uu___141_1122.nolabels);
          use_zfuel_name = (uu___141_1122.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___141_1122.encode_non_total_function_typ);
          current_module_name = (uu___141_1122.current_module_name)
        } in
      (fname, ftok, uu____1121)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___114_1157  ->
           match uu___114_1157 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1179 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1191 =
        lookup_binding env
          (fun uu___115_1193  ->
             match uu___115_1193 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1203 -> None) in
      FStar_All.pipe_right uu____1191 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1216 = try_lookup_lid env a in
      match uu____1216 with
      | None  ->
          let uu____1233 =
            let uu____1234 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1234 in
          failwith uu____1233
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
          let uu___142_1265 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___142_1265.depth);
            tcenv = (uu___142_1265.tcenv);
            warn = (uu___142_1265.warn);
            cache = (uu___142_1265.cache);
            nolabels = (uu___142_1265.nolabels);
            use_zfuel_name = (uu___142_1265.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___142_1265.encode_non_total_function_typ);
            current_module_name = (uu___142_1265.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1277 = lookup_lid env x in
        match uu____1277 with
        | (t1,t2,uu____1285) ->
            let t3 =
              let uu____1291 =
                let uu____1295 =
                  let uu____1297 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1297] in
                (f, uu____1295) in
              FStar_SMTEncoding_Util.mkApp uu____1291 in
            let uu___143_1300 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___143_1300.depth);
              tcenv = (uu___143_1300.tcenv);
              warn = (uu___143_1300.warn);
              cache = (uu___143_1300.cache);
              nolabels = (uu___143_1300.nolabels);
              use_zfuel_name = (uu___143_1300.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___143_1300.encode_non_total_function_typ);
              current_module_name = (uu___143_1300.current_module_name)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1310 = try_lookup_lid env l in
      match uu____1310 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1337 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1342,fuel::[]) ->
                         let uu____1345 =
                           let uu____1346 =
                             let uu____1347 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1347 Prims.fst in
                           FStar_Util.starts_with uu____1346 "fuel" in
                         if uu____1345
                         then
                           let uu____1349 =
                             let uu____1350 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1350
                               fuel in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1349
                         else Some t
                     | uu____1353 -> Some t)
                | uu____1354 -> None))
let lookup_free_var env a =
  let uu____1372 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1372 with
  | Some t -> t
  | None  ->
      let uu____1375 =
        let uu____1376 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1376 in
      failwith uu____1375
let lookup_free_var_name env a =
  let uu____1393 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1393 with | (x,uu____1400,uu____1401) -> x
let lookup_free_var_sym env a =
  let uu____1425 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1425 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1446;
             FStar_SMTEncoding_Term.rng = uu____1447;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1455 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1469 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___116_1478  ->
           match uu___116_1478 with
           | Binding_fvar (uu____1480,nm',tok,uu____1483) when nm = nm' ->
               tok
           | uu____1488 -> None)
let mkForall_fuel' n1 uu____1505 =
  match uu____1505 with
  | (pats,vars,body) ->
      let fallback uu____1521 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1524 = FStar_Options.unthrottle_inductives () in
      if uu____1524
      then fallback ()
      else
        (let uu____1526 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1526 with
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
                       | uu____1545 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1559 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1559
                     | uu____1561 ->
                         let uu____1562 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1562 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1565 -> body in
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
          let uu____1609 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1609 FStar_Option.isNone
      | uu____1622 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1629 =
        let uu____1630 = FStar_Syntax_Util.un_uinst t in
        uu____1630.FStar_Syntax_Syntax.n in
      match uu____1629 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1633,uu____1634,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___117_1663  ->
                  match uu___117_1663 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1664 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1665,uu____1666,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1693 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1693 FStar_Option.isSome
      | uu____1706 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1713 = head_normal env t in
      if uu____1713
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
    let uu____1724 =
      let uu____1728 = FStar_Syntax_Syntax.null_binder t in [uu____1728] in
    let uu____1729 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1724 uu____1729 None
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
                    let uu____1756 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1756
                | s ->
                    let uu____1759 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1759) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___118_1771  ->
    match uu___118_1771 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1772 -> false
let is_eta:
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term Prims.option
  =
  fun env  ->
    fun vars  ->
      fun t  ->
        let rec aux t1 xs =
          match ((t1.FStar_SMTEncoding_Term.tm), xs) with
          | (FStar_SMTEncoding_Term.App
             (app,f::{
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV y;
                       FStar_SMTEncoding_Term.freevars = uu____1800;
                       FStar_SMTEncoding_Term.rng = uu____1801;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              aux f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1815) ->
              let uu____1820 =
                ((FStar_List.length args) = (FStar_List.length vars)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1830 -> false) args vars) in
              if uu____1820 then tok_of_name env f else None
          | (uu____1833,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t1 in
              let uu____1836 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1838 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1838)) in
              if uu____1836 then Some t1 else None
          | uu____1841 -> None in
        aux t (FStar_List.rev vars)
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
      (let uu____1856 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____1856
       then
         let uu____1857 = FStar_Syntax_Print.term_to_string tm in
         let uu____1858 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____1857 uu____1858
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
    | uu____1940 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___119_1943  ->
    match uu___119_1943 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____1945 =
          let uu____1949 =
            let uu____1951 =
              let uu____1952 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____1952 in
            [uu____1951] in
          ("FStar.Char.Char", uu____1949) in
        FStar_SMTEncoding_Util.mkApp uu____1945
    | FStar_Const.Const_int (i,None ) ->
        let uu____1960 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____1960
    | FStar_Const.Const_int (i,Some uu____1962) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____1971) ->
        let uu____1974 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____1974
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____1978 =
          let uu____1979 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____1979 in
        failwith uu____1978
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1998 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2006 ->
            let uu____2011 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2011
        | uu____2012 ->
            if norm1
            then let uu____2013 = whnf env t1 in aux false uu____2013
            else
              (let uu____2015 =
                 let uu____2016 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2017 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2016 uu____2017 in
               failwith uu____2015) in
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
    | uu____2038 ->
        let uu____2039 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2039)
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
        (let uu____2182 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2182
         then
           let uu____2183 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2183
         else ());
        (let uu____2185 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2221  ->
                   fun b  ->
                     match uu____2221 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2264 =
                           let x = unmangle (Prims.fst b) in
                           let uu____2273 = gen_term_var env1 x in
                           match uu____2273 with
                           | (xxsym,xx,env') ->
                               let uu____2287 =
                                 let uu____2290 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2290 env1 xx in
                               (match uu____2287 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2264 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2185 with
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
          let uu____2378 = encode_term t env in
          match uu____2378 with
          | (t1,decls) ->
              let uu____2385 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2385, decls)
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
          let uu____2393 = encode_term t env in
          match uu____2393 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2402 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2402, decls)
               | Some f ->
                   let uu____2404 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2404, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2411 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2411
       then
         let uu____2412 = FStar_Syntax_Print.tag_of_term t in
         let uu____2413 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2414 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2412 uu____2413
           uu____2414
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2419 =
             let uu____2420 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2421 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2422 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2423 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2420
               uu____2421 uu____2422 uu____2423 in
           failwith uu____2419
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2427 =
             let uu____2428 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2428 in
           failwith uu____2427
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2433) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2463) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2472 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2472, [])
       | FStar_Syntax_Syntax.Tm_type uu____2478 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2481) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2487 = encode_const c in (uu____2487, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2502 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2502 with
            | (binders1,res) ->
                let uu____2509 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2509
                then
                  let uu____2512 = encode_binders None binders1 env in
                  (match uu____2512 with
                   | (vars,guards,env',decls,uu____2527) ->
                       let fsym =
                         let uu____2537 = varops.fresh "f" in
                         (uu____2537, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2540 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___144_2544 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___144_2544.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___144_2544.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___144_2544.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___144_2544.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___144_2544.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___144_2544.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___144_2544.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___144_2544.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___144_2544.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___144_2544.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___144_2544.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___144_2544.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___144_2544.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___144_2544.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___144_2544.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___144_2544.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___144_2544.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___144_2544.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___144_2544.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___144_2544.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___144_2544.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___144_2544.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___144_2544.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2540 with
                        | (pre_opt,res_t) ->
                            let uu____2551 =
                              encode_term_pred None res_t env' app in
                            (match uu____2551 with
                             | (res_pred,decls') ->
                                 let uu____2558 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2565 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2565, [])
                                   | Some pre ->
                                       let uu____2568 =
                                         encode_formula pre env' in
                                       (match uu____2568 with
                                        | (guard,decls0) ->
                                            let uu____2576 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2576, decls0)) in
                                 (match uu____2558 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2584 =
                                          let uu____2590 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2590) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2584 in
                                      let cvars =
                                        let uu____2600 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2600
                                          (FStar_List.filter
                                             (fun uu____2606  ->
                                                match uu____2606 with
                                                | (x,uu____2610) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2621 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2621 with
                                       | Some (t',sorts,uu____2637) ->
                                           let uu____2647 =
                                             let uu____2648 =
                                               let uu____2652 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               (t', uu____2652) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2648 in
                                           (uu____2647, [])
                                       | None  ->
                                           let tsym =
                                             let uu____2668 =
                                               let uu____2669 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2669 in
                                             varops.mk_unique uu____2668 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2676 =
                                               FStar_Options.log_queries () in
                                             if uu____2676
                                             then
                                               let uu____2678 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2678
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2684 =
                                               let uu____2688 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2688) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2684 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____2696 =
                                               let uu____2700 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2700, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2696 in
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
                                             let uu____2713 =
                                               let uu____2717 =
                                                 let uu____2718 =
                                                   let uu____2724 =
                                                     let uu____2725 =
                                                       let uu____2728 =
                                                         let uu____2729 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2729 in
                                                       (f_has_t, uu____2728) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2725 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2724) in
                                                 mkForall_fuel uu____2718 in
                                               (uu____2717,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2713 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____2742 =
                                               let uu____2746 =
                                                 let uu____2747 =
                                                   let uu____2753 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2753) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2747 in
                                               (uu____2746, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2742 in
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
                                              (tsym, cvar_sorts, t_decls);
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
                     let uu____2784 =
                       let uu____2788 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____2788, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Term.Assume uu____2784 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____2797 =
                       let uu____2801 =
                         let uu____2802 =
                           let uu____2808 =
                             let uu____2809 =
                               let uu____2812 =
                                 let uu____2813 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2813 in
                               (f_has_t, uu____2812) in
                             FStar_SMTEncoding_Util.mkImp uu____2809 in
                           ([[f_has_t]], [fsym], uu____2808) in
                         mkForall_fuel uu____2802 in
                       (uu____2801, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Term.Assume uu____2797 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2827 ->
           let uu____2832 =
             let uu____2835 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2835 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2840;
                 FStar_Syntax_Syntax.pos = uu____2841;
                 FStar_Syntax_Syntax.vars = uu____2842;_} ->
                 let uu____2849 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2849 with
                  | (b,f1) ->
                      let uu____2863 =
                        let uu____2864 = FStar_List.hd b in
                        Prims.fst uu____2864 in
                      (uu____2863, f1))
             | uu____2869 -> failwith "impossible" in
           (match uu____2832 with
            | (x,f) ->
                let uu____2876 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____2876 with
                 | (base_t,decls) ->
                     let uu____2883 = gen_term_var env x in
                     (match uu____2883 with
                      | (x1,xtm,env') ->
                          let uu____2892 = encode_formula f env' in
                          (match uu____2892 with
                           | (refinement,decls') ->
                               let uu____2899 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____2899 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____2910 =
                                        let uu____2912 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____2916 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____2912
                                          uu____2916 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____2910 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____2932  ->
                                              match uu____2932 with
                                              | (y,uu____2936) ->
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
                                    let uu____2955 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2955 with
                                     | Some (t1,uu____2970,uu____2971) ->
                                         let uu____2981 =
                                           let uu____2982 =
                                             let uu____2986 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             (t1, uu____2986) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2982 in
                                         (uu____2981, [])
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3003 =
                                             let uu____3004 =
                                               let uu____3005 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3005 in
                                             Prims.strcat module_name
                                               uu____3004 in
                                           varops.mk_unique uu____3003 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3014 =
                                             let uu____3018 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3018) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3014 in
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
                                           let uu____3028 =
                                             let uu____3032 =
                                               let uu____3033 =
                                                 let uu____3039 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3039) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3033 in
                                             (uu____3032,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3028 in
                                         let t_kinding =
                                           let uu____3049 =
                                             let uu____3053 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3053,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3049 in
                                         let t_interp =
                                           let uu____3063 =
                                             let uu____3067 =
                                               let uu____3068 =
                                                 let uu____3074 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3074) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3068 in
                                             let uu____3086 =
                                               let uu____3088 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3088 in
                                             (uu____3067, uu____3086,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3063 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         (FStar_Util.smap_add env.cache
                                            tkey_hash
                                            (tsym, cvar_sorts, t_decls);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3116 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3116 in
           let uu____3120 = encode_term_pred None k env ttm in
           (match uu____3120 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3128 =
                    let uu____3132 =
                      let uu____3133 =
                        let uu____3134 =
                          let uu____3135 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3135 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3134 in
                      varops.mk_unique uu____3133 in
                    (t_has_k, (Some "Uvar typing"), uu____3132) in
                  FStar_SMTEncoding_Term.Assume uu____3128 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3141 ->
           let uu____3151 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3151 with
            | (head1,args_e) ->
                let uu____3179 =
                  let uu____3187 =
                    let uu____3188 = FStar_Syntax_Subst.compress head1 in
                    uu____3188.FStar_Syntax_Syntax.n in
                  (uu____3187, args_e) in
                (match uu____3179 with
                 | (uu____3198,uu____3199) when head_redex env head1 ->
                     let uu____3210 = whnf env t in
                     encode_term uu____3210 env
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
                     let uu____3284 = encode_term v1 env in
                     (match uu____3284 with
                      | (v11,decls1) ->
                          let uu____3291 = encode_term v2 env in
                          (match uu____3291 with
                           | (v21,decls2) ->
                               let uu____3298 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3298,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3300) ->
                     let e0 =
                       let uu____3314 =
                         let uu____3317 =
                           let uu____3318 =
                             let uu____3328 =
                               let uu____3334 = FStar_List.hd args_e in
                               [uu____3334] in
                             (head1, uu____3328) in
                           FStar_Syntax_Syntax.Tm_app uu____3318 in
                         FStar_Syntax_Syntax.mk uu____3317 in
                       uu____3314 None head1.FStar_Syntax_Syntax.pos in
                     ((let uu____3367 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3367
                       then
                         let uu____3368 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Trying to normalize %s\n"
                           uu____3368
                       else ());
                      (let e01 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Reify;
                           FStar_TypeChecker_Normalize.Eager_unfolding;
                           FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                           env.tcenv e0 in
                       (let uu____3372 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify") in
                        if uu____3372
                        then
                          let uu____3373 =
                            FStar_Syntax_Print.term_to_string e01 in
                          FStar_Util.print1 "Result of normalization %s\n"
                            uu____3373
                        else ());
                       (let e02 =
                          let uu____3376 =
                            let uu____3377 =
                              let uu____3378 =
                                FStar_Syntax_Subst.compress e01 in
                              uu____3378.FStar_Syntax_Syntax.n in
                            match uu____3377 with
                            | FStar_Syntax_Syntax.Tm_app uu____3381 -> false
                            | uu____3391 -> true in
                          if uu____3376
                          then e01
                          else
                            (let uu____3393 =
                               FStar_Syntax_Util.head_and_args e01 in
                             match uu____3393 with
                             | (head2,args) ->
                                 let uu____3419 =
                                   let uu____3420 =
                                     let uu____3421 =
                                       FStar_Syntax_Subst.compress head2 in
                                     uu____3421.FStar_Syntax_Syntax.n in
                                   match uu____3420 with
                                   | FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_reify ) -> true
                                   | uu____3424 -> false in
                                 if uu____3419
                                 then
                                   (match args with
                                    | x::[] -> Prims.fst x
                                    | uu____3440 ->
                                        failwith
                                          "Impossible : Reify applied to multiple arguments after normalization.")
                                 else e01) in
                        let e =
                          match args_e with
                          | uu____3448::[] -> e02
                          | uu____3461 ->
                              let uu____3467 =
                                let uu____3470 =
                                  let uu____3471 =
                                    let uu____3481 = FStar_List.tl args_e in
                                    (e02, uu____3481) in
                                  FStar_Syntax_Syntax.Tm_app uu____3471 in
                                FStar_Syntax_Syntax.mk uu____3470 in
                              uu____3467 None t0.FStar_Syntax_Syntax.pos in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3504),(arg,uu____3506)::[]) -> encode_term arg env
                 | uu____3524 ->
                     let uu____3532 = encode_args args_e env in
                     (match uu____3532 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3565 = encode_term head1 env in
                            match uu____3565 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3604 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3604 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3646  ->
                                                 fun uu____3647  ->
                                                   match (uu____3646,
                                                           uu____3647)
                                                   with
                                                   | ((bv,uu____3661),
                                                      (a,uu____3663)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3677 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3677
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3682 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3682 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3692 =
                                                   let uu____3696 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3701 =
                                                     let uu____3702 =
                                                       let uu____3703 =
                                                         let uu____3704 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3704 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3703 in
                                                     varops.mk_unique
                                                       uu____3702 in
                                                   (uu____3696,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3701) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3692 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3721 = lookup_free_var_sym env fv in
                            match uu____3721 with
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
                                let uu____3759 =
                                  let uu____3760 =
                                    let uu____3763 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3763 Prims.fst in
                                  FStar_All.pipe_right uu____3760 Prims.snd in
                                Some uu____3759
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3782,(FStar_Util.Inl t1,uu____3784),uu____3785)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3823,(FStar_Util.Inr c,uu____3825),uu____3826)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3864 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3884 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3884 in
                               let uu____3885 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3885 with
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
                                     | uu____3910 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3955 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3955 with
            | (bs1,body1,opening) ->
                let fallback uu____3970 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3975 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3975, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3986 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3986
                  | FStar_Util.Inr (eff,uu____3988) ->
                      let uu____3994 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3994 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body = reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4039 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___145_4040 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___145_4040.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___145_4040.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___145_4040.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___145_4040.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___145_4040.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___145_4040.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___145_4040.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___145_4040.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___145_4040.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___145_4040.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___145_4040.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___145_4040.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___145_4040.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___145_4040.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___145_4040.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___145_4040.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___145_4040.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___145_4040.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___145_4040.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___145_4040.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___145_4040.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___145_4040.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___145_4040.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4039 FStar_Syntax_Syntax.U_unknown in
                        let uu____4041 =
                          let uu____4042 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4042 in
                        FStar_Util.Inl uu____4041
                    | FStar_Util.Inr (eff_name,uu____4049) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4080 =
                        let uu____4081 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4081 in
                      FStar_All.pipe_right uu____4080
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4093 =
                        let uu____4094 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4094 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4102 =
                          let uu____4103 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4103 in
                        FStar_All.pipe_right uu____4102
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4107 =
                             let uu____4108 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4108 in
                           FStar_All.pipe_right uu____4107
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4119 =
                         let uu____4120 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4120 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4119);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4135 =
                       (is_impure lc1) &&
                         (let uu____4136 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4136) in
                     if uu____4135
                     then fallback ()
                     else
                       (let uu____4140 = encode_binders None bs1 env in
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
                                      let key_body =
                                        let uu____4203 =
                                          let uu____4209 =
                                            let uu____4210 =
                                              let uu____4213 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____4213, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____4210 in
                                          ([], vars, uu____4209) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4203 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____4224 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____4224 with
                                       | Some (t1,uu____4239,uu____4240) ->
                                           let uu____4250 =
                                             let uu____4251 =
                                               let uu____4255 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (t1, uu____4255) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4251 in
                                           (uu____4250, [])
                                       | None  ->
                                           let uu____4266 =
                                             is_eta env vars body3 in
                                           (match uu____4266 with
                                            | Some t1 -> (t1, [])
                                            | None  ->
                                                let cvar_sorts =
                                                  FStar_List.map Prims.snd
                                                    cvars in
                                                let fsym =
                                                  let module_name =
                                                    env.current_module_name in
                                                  let fsym =
                                                    let uu____4279 =
                                                      let uu____4280 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____4280 in
                                                    varops.mk_unique
                                                      uu____4279 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      None) in
                                                let f =
                                                  let uu____4285 =
                                                    let uu____4289 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars in
                                                    (fsym, uu____4289) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4285 in
                                                let app = mk_Apply f vars in
                                                let typing_f =
                                                  let uu____4297 =
                                                    codomain_eff lc2 in
                                                  match uu____4297 with
                                                  | None  -> []
                                                  | Some c ->
                                                      let tfun =
                                                        FStar_Syntax_Util.arrow
                                                          bs1 c in
                                                      let uu____4304 =
                                                        encode_term_pred None
                                                          tfun env f in
                                                      (match uu____4304 with
                                                       | (f_has_t,decls'') ->
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym in
                                                           let uu____4311 =
                                                             let uu____4313 =
                                                               let uu____4314
                                                                 =
                                                                 let uu____4318
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkForall
                                                                    ([[f]],
                                                                    cvars,
                                                                    f_has_t) in
                                                                 (uu____4318,
                                                                   (Some
                                                                    a_name),
                                                                   a_name) in
                                                               FStar_SMTEncoding_Term.Assume
                                                                 uu____4314 in
                                                             [uu____4313] in
                                                           FStar_List.append
                                                             decls''
                                                             uu____4311) in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____4326 =
                                                    let uu____4330 =
                                                      let uu____4331 =
                                                        let uu____4337 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars),
                                                          uu____4337) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____4331 in
                                                    (uu____4330,
                                                      (Some a_name), a_name) in
                                                  FStar_SMTEncoding_Term.Assume
                                                    uu____4326 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          (fdecl :: typing_f)
                                                          [interp_f])) in
                                                (FStar_Util.smap_add
                                                   env.cache tkey_hash
                                                   (fsym, cvar_sorts,
                                                     f_decls);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4355,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4356;
                          FStar_Syntax_Syntax.lbunivs = uu____4357;
                          FStar_Syntax_Syntax.lbtyp = uu____4358;
                          FStar_Syntax_Syntax.lbeff = uu____4359;
                          FStar_Syntax_Syntax.lbdef = uu____4360;_}::uu____4361),uu____4362)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4380;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4382;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4398 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4411 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4411, [decl_e])))
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
              let uu____4453 = encode_term e1 env in
              match uu____4453 with
              | (ee1,decls1) ->
                  let uu____4460 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4460 with
                   | (xs,e21) ->
                       let uu____4474 = FStar_List.hd xs in
                       (match uu____4474 with
                        | (x1,uu____4482) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4484 = encode_body e21 env' in
                            (match uu____4484 with
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
            let uu____4506 =
              let uu____4510 =
                let uu____4511 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4511 in
              gen_term_var env uu____4510 in
            match uu____4506 with
            | (scrsym,scr',env1) ->
                let uu____4525 = encode_term e env1 in
                (match uu____4525 with
                 | (scr,decls) ->
                     let uu____4532 =
                       let encode_branch b uu____4548 =
                         match uu____4548 with
                         | (else_case,decls1) ->
                             let uu____4559 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4559 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4589  ->
                                       fun uu____4590  ->
                                         match (uu____4589, uu____4590) with
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
                                                       fun uu____4627  ->
                                                         match uu____4627
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4632 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4647 =
                                                     encode_term w1 env2 in
                                                   (match uu____4647 with
                                                    | (w2,decls21) ->
                                                        let uu____4655 =
                                                          let uu____4656 =
                                                            let uu____4659 =
                                                              let uu____4660
                                                                =
                                                                let uu____4663
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4663) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4660 in
                                                            (guard,
                                                              uu____4659) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4656 in
                                                        (uu____4655, decls21)) in
                                             (match uu____4632 with
                                              | (guard1,decls21) ->
                                                  let uu____4671 =
                                                    encode_br br env2 in
                                                  (match uu____4671 with
                                                   | (br1,decls3) ->
                                                       let uu____4679 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4679,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4532 with
                      | (match_tm,decls1) ->
                          let uu____4691 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4691, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4722 -> let uu____4723 = encode_one_pat env pat in [uu____4723]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4735 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4735
       then
         let uu____4736 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4736
       else ());
      (let uu____4738 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4738 with
       | (vars,pat_term) ->
           let uu____4748 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4771  ->
                     fun v1  ->
                       match uu____4771 with
                       | (env1,vars1) ->
                           let uu____4799 = gen_term_var env1 v1 in
                           (match uu____4799 with
                            | (xx,uu____4811,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4748 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4858 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4866 =
                        let uu____4869 = encode_const c in
                        (scrutinee, uu____4869) in
                      FStar_SMTEncoding_Util.mkEq uu____4866
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4888 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4888 with
                        | (uu____4892,uu____4893::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4895 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4916  ->
                                  match uu____4916 with
                                  | (arg,uu____4922) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4932 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4932)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4951 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4966 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4981 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5003  ->
                                  match uu____5003 with
                                  | (arg,uu____5012) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5022 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5022)) in
                      FStar_All.pipe_right uu____4981 FStar_List.flatten in
                let pat_term1 uu____5038 = encode_term pat_term env1 in
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
      let uu____5045 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5060  ->
                fun uu____5061  ->
                  match (uu____5060, uu____5061) with
                  | ((tms,decls),(t,uu____5081)) ->
                      let uu____5092 = encode_term t env in
                      (match uu____5092 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5045 with | (l1,decls) -> ((FStar_List.rev l1), decls)
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
            let uu____5130 = FStar_Syntax_Util.list_elements e in
            match uu____5130 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 []) in
          let one_pat p =
            let uu____5148 =
              let uu____5158 = FStar_Syntax_Util.unmeta p in
              FStar_All.pipe_right uu____5158 FStar_Syntax_Util.head_and_args in
            match uu____5148 with
            | (head1,args) ->
                let uu____5189 =
                  let uu____5197 =
                    let uu____5198 = FStar_Syntax_Util.un_uinst head1 in
                    uu____5198.FStar_Syntax_Syntax.n in
                  (uu____5197, args) in
                (match uu____5189 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5212,uu____5213)::(e,uu____5215)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5246)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5267 -> failwith "Unexpected pattern term") in
          let lemma_pats p =
            let elts = list_elements1 p in
            let smt_pat_or t1 =
              let uu____5300 =
                let uu____5310 = FStar_Syntax_Util.unmeta t1 in
                FStar_All.pipe_right uu____5310
                  FStar_Syntax_Util.head_and_args in
              match uu____5300 with
              | (head1,args) ->
                  let uu____5339 =
                    let uu____5347 =
                      let uu____5348 = FStar_Syntax_Util.un_uinst head1 in
                      uu____5348.FStar_Syntax_Syntax.n in
                    (uu____5347, args) in
                  (match uu____5339 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5361)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5381 -> None) in
            match elts with
            | t1::[] ->
                let uu____5399 = smt_pat_or t1 in
                (match uu____5399 with
                 | Some e ->
                     let uu____5415 = list_elements1 e in
                     FStar_All.pipe_right uu____5415
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5432 = list_elements1 branch1 in
                             FStar_All.pipe_right uu____5432
                               (FStar_List.map one_pat)))
                 | uu____5446 ->
                     let uu____5450 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat) in
                     [uu____5450])
            | uu____5481 ->
                let uu____5483 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat) in
                [uu____5483] in
          let uu____5514 =
            let uu____5530 =
              let uu____5531 = FStar_Syntax_Subst.compress t in
              uu____5531.FStar_Syntax_Syntax.n in
            match uu____5530 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5561 = FStar_Syntax_Subst.open_comp binders c in
                (match uu____5561 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5596;
                            FStar_Syntax_Syntax.effect_name = uu____5597;
                            FStar_Syntax_Syntax.result_typ = uu____5598;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5600)::(post,uu____5602)::(pats,uu____5604)::[];
                            FStar_Syntax_Syntax.flags = uu____5605;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats in
                          let uu____5639 = lemma_pats pats' in
                          (binders1, pre, post, uu____5639)
                      | uu____5658 -> failwith "impos"))
            | uu____5674 -> failwith "Impos" in
          match uu____5514 with
          | (binders,pre,post,patterns) ->
              let uu____5718 = encode_binders None binders env in
              (match uu____5718 with
               | (vars,guards,env1,decls,uu____5733) ->
                   let uu____5740 =
                     let uu____5747 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5778 =
                                 let uu____5783 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5799  ->
                                           match uu____5799 with
                                           | (t1,uu____5806) ->
                                               encode_term t1
                                                 (let uu___146_5809 = env1 in
                                                  {
                                                    bindings =
                                                      (uu___146_5809.bindings);
                                                    depth =
                                                      (uu___146_5809.depth);
                                                    tcenv =
                                                      (uu___146_5809.tcenv);
                                                    warn =
                                                      (uu___146_5809.warn);
                                                    cache =
                                                      (uu___146_5809.cache);
                                                    nolabels =
                                                      (uu___146_5809.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___146_5809.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___146_5809.current_module_name)
                                                  }))) in
                                 FStar_All.pipe_right uu____5783
                                   FStar_List.unzip in
                               match uu____5778 with
                               | (pats,decls1) -> (pats, decls1))) in
                     FStar_All.pipe_right uu____5747 FStar_List.unzip in
                   (match uu____5740 with
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
                                           let uu____5873 =
                                             let uu____5874 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5874 e in
                                           uu____5873 :: p))
                               | uu____5875 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5904 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e in
                                                 uu____5904 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5912 =
                                           let uu____5913 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort) in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5913 tl1 in
                                         aux uu____5912 vars2
                                     | uu____5914 -> pats in
                                   let uu____5918 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort) in
                                   aux uu____5918 vars) in
                        let env2 =
                          let uu___147_5920 = env1 in
                          {
                            bindings = (uu___147_5920.bindings);
                            depth = (uu___147_5920.depth);
                            tcenv = (uu___147_5920.tcenv);
                            warn = (uu___147_5920.warn);
                            cache = (uu___147_5920.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___147_5920.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___147_5920.encode_non_total_function_typ);
                            current_module_name =
                              (uu___147_5920.current_module_name)
                          } in
                        let uu____5921 =
                          let uu____5924 = FStar_Syntax_Util.unmeta pre in
                          encode_formula uu____5924 env2 in
                        (match uu____5921 with
                         | (pre1,decls'') ->
                             let uu____5929 =
                               let uu____5932 = FStar_Syntax_Util.unmeta post in
                               encode_formula uu____5932 env2 in
                             (match uu____5929 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls''')) in
                                  let uu____5939 =
                                    let uu____5940 =
                                      let uu____5946 =
                                        let uu____5947 =
                                          let uu____5950 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards) in
                                          (uu____5950, post1) in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5947 in
                                      (pats1, vars, uu____5946) in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5940 in
                                  (uu____5939, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5963 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5963
        then
          let uu____5964 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5965 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5964 uu____5965
        else () in
      let enc f r l =
        let uu____5992 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6005 = encode_term (Prims.fst x) env in
                 match uu____6005 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5992 with
        | (decls,args) ->
            let uu____6022 =
              let uu___148_6023 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___148_6023.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___148_6023.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6022, decls) in
      let const_op f r uu____6042 = let uu____6045 = f r in (uu____6045, []) in
      let un_op f l =
        let uu____6061 = FStar_List.hd l in FStar_All.pipe_left f uu____6061 in
      let bin_op f uu___120_6074 =
        match uu___120_6074 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6082 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6109 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6118  ->
                 match uu____6118 with
                 | (t,uu____6126) ->
                     let uu____6127 = encode_formula t env in
                     (match uu____6127 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6109 with
        | (decls,phis) ->
            let uu____6144 =
              let uu___149_6145 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___149_6145.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___149_6145.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6144, decls) in
      let eq_op r uu___121_6161 =
        match uu___121_6161 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6221 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6221 r [e1; e2]
        | l ->
            let uu____6241 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6241 r l in
      let mk_imp1 r uu___122_6260 =
        match uu___122_6260 with
        | (lhs,uu____6264)::(rhs,uu____6266)::[] ->
            let uu____6287 = encode_formula rhs env in
            (match uu____6287 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6296) ->
                      (l1, decls1)
                  | uu____6299 ->
                      let uu____6300 = encode_formula lhs env in
                      (match uu____6300 with
                       | (l2,decls2) ->
                           let uu____6307 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6307, (FStar_List.append decls1 decls2)))))
        | uu____6309 -> failwith "impossible" in
      let mk_ite r uu___123_6324 =
        match uu___123_6324 with
        | (guard,uu____6328)::(_then,uu____6330)::(_else,uu____6332)::[] ->
            let uu____6361 = encode_formula guard env in
            (match uu____6361 with
             | (g,decls1) ->
                 let uu____6368 = encode_formula _then env in
                 (match uu____6368 with
                  | (t,decls2) ->
                      let uu____6375 = encode_formula _else env in
                      (match uu____6375 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6384 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6403 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6403 in
      let connectives =
        let uu____6415 =
          let uu____6424 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6424) in
        let uu____6437 =
          let uu____6447 =
            let uu____6456 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6456) in
          let uu____6469 =
            let uu____6479 =
              let uu____6489 =
                let uu____6498 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6498) in
              let uu____6511 =
                let uu____6521 =
                  let uu____6531 =
                    let uu____6540 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6540) in
                  [uu____6531;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6521 in
              uu____6489 :: uu____6511 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6479 in
          uu____6447 :: uu____6469 in
        uu____6415 :: uu____6437 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6702 = encode_formula phi' env in
            (match uu____6702 with
             | (phi2,decls) ->
                 let uu____6709 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6709, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6710 ->
            let uu____6715 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6715 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6744 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6744 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6752;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6754;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6770 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6770 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6802::(x,uu____6804)::(t,uu____6806)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6840 = encode_term x env in
                 (match uu____6840 with
                  | (x1,decls) ->
                      let uu____6847 = encode_term t env in
                      (match uu____6847 with
                       | (t1,decls') ->
                           let uu____6854 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6854, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6858)::(msg,uu____6860)::(phi2,uu____6862)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6896 =
                   let uu____6899 =
                     let uu____6900 = FStar_Syntax_Subst.compress r in
                     uu____6900.FStar_Syntax_Syntax.n in
                   let uu____6903 =
                     let uu____6904 = FStar_Syntax_Subst.compress msg in
                     uu____6904.FStar_Syntax_Syntax.n in
                   (uu____6899, uu____6903) in
                 (match uu____6896 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6911))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6927 -> fallback phi2)
             | uu____6930 when head_redex env head2 ->
                 let uu____6938 = whnf env phi1 in
                 encode_formula uu____6938 env
             | uu____6939 ->
                 let uu____6947 = encode_term phi1 env in
                 (match uu____6947 with
                  | (tt,decls) ->
                      let uu____6954 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___150_6955 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___150_6955.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___150_6955.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6954, decls)))
        | uu____6958 ->
            let uu____6959 = encode_term phi1 env in
            (match uu____6959 with
             | (tt,decls) ->
                 let uu____6966 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___151_6967 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___151_6967.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___151_6967.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6966, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6994 = encode_binders None bs env1 in
        match uu____6994 with
        | (vars,guards,env2,decls,uu____7016) ->
            let uu____7023 =
              let uu____7030 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7053 =
                          let uu____7058 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7072  ->
                                    match uu____7072 with
                                    | (t,uu____7078) ->
                                        encode_term t
                                          (let uu___152_7079 = env2 in
                                           {
                                             bindings =
                                               (uu___152_7079.bindings);
                                             depth = (uu___152_7079.depth);
                                             tcenv = (uu___152_7079.tcenv);
                                             warn = (uu___152_7079.warn);
                                             cache = (uu___152_7079.cache);
                                             nolabels =
                                               (uu___152_7079.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___152_7079.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___152_7079.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7058 FStar_List.unzip in
                        match uu____7053 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7030 FStar_List.unzip in
            (match uu____7023 with
             | (pats,decls') ->
                 let uu____7131 = encode_formula body env2 in
                 (match uu____7131 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7150;
                             FStar_SMTEncoding_Term.rng = uu____7151;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7159 -> guards in
                      let uu____7162 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7162, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7196  ->
                   match uu____7196 with
                   | (x,uu____7200) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7206 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7212 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7212) uu____7206 tl1 in
             let uu____7214 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7226  ->
                       match uu____7226 with
                       | (b,uu____7230) ->
                           let uu____7231 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7231)) in
             (match uu____7214 with
              | None  -> ()
              | Some (x,uu____7235) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7245 =
                    let uu____7246 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7246 in
                  FStar_Errors.warn pos uu____7245) in
       let uu____7247 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7247 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7253 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7289  ->
                     match uu____7289 with
                     | (l,uu____7299) -> FStar_Ident.lid_equals op l)) in
           (match uu____7253 with
            | None  -> fallback phi1
            | Some (uu____7322,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7351 = encode_q_body env vars pats body in
             match uu____7351 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7377 =
                     let uu____7383 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7383) in
                   FStar_SMTEncoding_Term.mkForall uu____7377
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7395 = encode_q_body env vars pats body in
             match uu____7395 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7420 =
                   let uu____7421 =
                     let uu____7427 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7427) in
                   FStar_SMTEncoding_Term.mkExists uu____7421
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7420, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7476 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7476 with
  | (asym,a) ->
      let uu____7481 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7481 with
       | (xsym,x) ->
           let uu____7486 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7486 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7516 =
                      let uu____7522 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7522, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7516 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7537 =
                      let uu____7541 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7541) in
                    FStar_SMTEncoding_Util.mkApp uu____7537 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7549 =
                    let uu____7551 =
                      let uu____7553 =
                        let uu____7555 =
                          let uu____7556 =
                            let uu____7560 =
                              let uu____7561 =
                                let uu____7567 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7567) in
                              FStar_SMTEncoding_Util.mkForall uu____7561 in
                            (uu____7560, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Term.Assume uu____7556 in
                        let uu____7576 =
                          let uu____7578 =
                            let uu____7579 =
                              let uu____7583 =
                                let uu____7584 =
                                  let uu____7590 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7590) in
                                FStar_SMTEncoding_Util.mkForall uu____7584 in
                              (uu____7583,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Term.Assume uu____7579 in
                          [uu____7578] in
                        uu____7555 :: uu____7576 in
                      xtok_decl :: uu____7553 in
                    xname_decl :: uu____7551 in
                  (xtok1, uu____7549) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7639 =
                    let uu____7647 =
                      let uu____7653 =
                        let uu____7654 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7654 in
                      quant axy uu____7653 in
                    (FStar_Syntax_Const.op_Eq, uu____7647) in
                  let uu____7660 =
                    let uu____7669 =
                      let uu____7677 =
                        let uu____7683 =
                          let uu____7684 =
                            let uu____7685 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7685 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7684 in
                        quant axy uu____7683 in
                      (FStar_Syntax_Const.op_notEq, uu____7677) in
                    let uu____7691 =
                      let uu____7700 =
                        let uu____7708 =
                          let uu____7714 =
                            let uu____7715 =
                              let uu____7716 =
                                let uu____7719 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7720 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7719, uu____7720) in
                              FStar_SMTEncoding_Util.mkLT uu____7716 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7715 in
                          quant xy uu____7714 in
                        (FStar_Syntax_Const.op_LT, uu____7708) in
                      let uu____7726 =
                        let uu____7735 =
                          let uu____7743 =
                            let uu____7749 =
                              let uu____7750 =
                                let uu____7751 =
                                  let uu____7754 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7755 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7754, uu____7755) in
                                FStar_SMTEncoding_Util.mkLTE uu____7751 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7750 in
                            quant xy uu____7749 in
                          (FStar_Syntax_Const.op_LTE, uu____7743) in
                        let uu____7761 =
                          let uu____7770 =
                            let uu____7778 =
                              let uu____7784 =
                                let uu____7785 =
                                  let uu____7786 =
                                    let uu____7789 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7790 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7789, uu____7790) in
                                  FStar_SMTEncoding_Util.mkGT uu____7786 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7785 in
                              quant xy uu____7784 in
                            (FStar_Syntax_Const.op_GT, uu____7778) in
                          let uu____7796 =
                            let uu____7805 =
                              let uu____7813 =
                                let uu____7819 =
                                  let uu____7820 =
                                    let uu____7821 =
                                      let uu____7824 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7825 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7824, uu____7825) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7821 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7820 in
                                quant xy uu____7819 in
                              (FStar_Syntax_Const.op_GTE, uu____7813) in
                            let uu____7831 =
                              let uu____7840 =
                                let uu____7848 =
                                  let uu____7854 =
                                    let uu____7855 =
                                      let uu____7856 =
                                        let uu____7859 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7860 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7859, uu____7860) in
                                      FStar_SMTEncoding_Util.mkSub uu____7856 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7855 in
                                  quant xy uu____7854 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7848) in
                              let uu____7866 =
                                let uu____7875 =
                                  let uu____7883 =
                                    let uu____7889 =
                                      let uu____7890 =
                                        let uu____7891 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7891 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7890 in
                                    quant qx uu____7889 in
                                  (FStar_Syntax_Const.op_Minus, uu____7883) in
                                let uu____7897 =
                                  let uu____7906 =
                                    let uu____7914 =
                                      let uu____7920 =
                                        let uu____7921 =
                                          let uu____7922 =
                                            let uu____7925 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7926 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7925, uu____7926) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7922 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7921 in
                                      quant xy uu____7920 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7914) in
                                  let uu____7932 =
                                    let uu____7941 =
                                      let uu____7949 =
                                        let uu____7955 =
                                          let uu____7956 =
                                            let uu____7957 =
                                              let uu____7960 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7961 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7960, uu____7961) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7957 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7956 in
                                        quant xy uu____7955 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7949) in
                                    let uu____7967 =
                                      let uu____7976 =
                                        let uu____7984 =
                                          let uu____7990 =
                                            let uu____7991 =
                                              let uu____7992 =
                                                let uu____7995 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7996 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7995, uu____7996) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7992 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7991 in
                                          quant xy uu____7990 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7984) in
                                      let uu____8002 =
                                        let uu____8011 =
                                          let uu____8019 =
                                            let uu____8025 =
                                              let uu____8026 =
                                                let uu____8027 =
                                                  let uu____8030 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8031 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8030, uu____8031) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8027 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8026 in
                                            quant xy uu____8025 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8019) in
                                        let uu____8037 =
                                          let uu____8046 =
                                            let uu____8054 =
                                              let uu____8060 =
                                                let uu____8061 =
                                                  let uu____8062 =
                                                    let uu____8065 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8066 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8065, uu____8066) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8062 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8061 in
                                              quant xy uu____8060 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8054) in
                                          let uu____8072 =
                                            let uu____8081 =
                                              let uu____8089 =
                                                let uu____8095 =
                                                  let uu____8096 =
                                                    let uu____8097 =
                                                      let uu____8100 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8101 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8100,
                                                        uu____8101) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8097 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8096 in
                                                quant xy uu____8095 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8089) in
                                            let uu____8107 =
                                              let uu____8116 =
                                                let uu____8124 =
                                                  let uu____8130 =
                                                    let uu____8131 =
                                                      let uu____8132 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8132 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8131 in
                                                  quant qx uu____8130 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8124) in
                                              [uu____8116] in
                                            uu____8081 :: uu____8107 in
                                          uu____8046 :: uu____8072 in
                                        uu____8011 :: uu____8037 in
                                      uu____7976 :: uu____8002 in
                                    uu____7941 :: uu____7967 in
                                  uu____7906 :: uu____7932 in
                                uu____7875 :: uu____7897 in
                              uu____7840 :: uu____7866 in
                            uu____7805 :: uu____7831 in
                          uu____7770 :: uu____7796 in
                        uu____7735 :: uu____7761 in
                      uu____7700 :: uu____7726 in
                    uu____7669 :: uu____7691 in
                  uu____7639 :: uu____7660 in
                let mk1 l v1 =
                  let uu____8260 =
                    let uu____8265 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8297  ->
                              match uu____8297 with
                              | (l',uu____8306) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8265
                      (FStar_Option.map
                         (fun uu____8339  ->
                            match uu____8339 with | (uu____8350,b) -> b v1)) in
                  FStar_All.pipe_right uu____8260 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8391  ->
                          match uu____8391 with
                          | (l',uu____8400) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8426 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8426 with
        | (xxsym,xx) ->
            let uu____8431 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8431 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8439 =
                   let uu____8443 =
                     let uu____8444 =
                       let uu____8450 =
                         let uu____8451 =
                           let uu____8454 =
                             let uu____8455 =
                               let uu____8458 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8458) in
                             FStar_SMTEncoding_Util.mkEq uu____8455 in
                           (xx_has_type, uu____8454) in
                         FStar_SMTEncoding_Util.mkImp uu____8451 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8450) in
                     FStar_SMTEncoding_Util.mkForall uu____8444 in
                   let uu____8471 =
                     let uu____8472 =
                       let uu____8473 =
                         let uu____8474 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8474 in
                       Prims.strcat module_name uu____8473 in
                     varops.mk_unique uu____8472 in
                   (uu____8443, (Some "pretyping"), uu____8471) in
                 FStar_SMTEncoding_Term.Assume uu____8439)
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
    let uu____8504 =
      let uu____8505 =
        let uu____8509 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8509, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Term.Assume uu____8505 in
    let uu____8511 =
      let uu____8513 =
        let uu____8514 =
          let uu____8518 =
            let uu____8519 =
              let uu____8525 =
                let uu____8526 =
                  let uu____8529 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8529) in
                FStar_SMTEncoding_Util.mkImp uu____8526 in
              ([[typing_pred]], [xx], uu____8525) in
            mkForall_fuel uu____8519 in
          (uu____8518, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8514 in
      [uu____8513] in
    uu____8504 :: uu____8511 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8557 =
      let uu____8558 =
        let uu____8562 =
          let uu____8563 =
            let uu____8569 =
              let uu____8572 =
                let uu____8574 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8574] in
              [uu____8572] in
            let uu____8577 =
              let uu____8578 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8578 tt in
            (uu____8569, [bb], uu____8577) in
          FStar_SMTEncoding_Util.mkForall uu____8563 in
        (uu____8562, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Term.Assume uu____8558 in
    let uu____8589 =
      let uu____8591 =
        let uu____8592 =
          let uu____8596 =
            let uu____8597 =
              let uu____8603 =
                let uu____8604 =
                  let uu____8607 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8607) in
                FStar_SMTEncoding_Util.mkImp uu____8604 in
              ([[typing_pred]], [xx], uu____8603) in
            mkForall_fuel uu____8597 in
          (uu____8596, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8592 in
      [uu____8591] in
    uu____8557 :: uu____8589 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8641 =
        let uu____8642 =
          let uu____8646 =
            let uu____8648 =
              let uu____8650 =
                let uu____8652 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8653 =
                  let uu____8655 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8655] in
                uu____8652 :: uu____8653 in
              tt :: uu____8650 in
            tt :: uu____8648 in
          ("Prims.Precedes", uu____8646) in
        FStar_SMTEncoding_Util.mkApp uu____8642 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8641 in
    let precedes_y_x =
      let uu____8658 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8658 in
    let uu____8660 =
      let uu____8661 =
        let uu____8665 =
          let uu____8666 =
            let uu____8672 =
              let uu____8675 =
                let uu____8677 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8677] in
              [uu____8675] in
            let uu____8680 =
              let uu____8681 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8681 tt in
            (uu____8672, [bb], uu____8680) in
          FStar_SMTEncoding_Util.mkForall uu____8666 in
        (uu____8665, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Term.Assume uu____8661 in
    let uu____8692 =
      let uu____8694 =
        let uu____8695 =
          let uu____8699 =
            let uu____8700 =
              let uu____8706 =
                let uu____8707 =
                  let uu____8710 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8710) in
                FStar_SMTEncoding_Util.mkImp uu____8707 in
              ([[typing_pred]], [xx], uu____8706) in
            mkForall_fuel uu____8700 in
          (uu____8699, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8695 in
      let uu____8723 =
        let uu____8725 =
          let uu____8726 =
            let uu____8730 =
              let uu____8731 =
                let uu____8737 =
                  let uu____8738 =
                    let uu____8741 =
                      let uu____8742 =
                        let uu____8744 =
                          let uu____8746 =
                            let uu____8748 =
                              let uu____8749 =
                                let uu____8752 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8753 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8752, uu____8753) in
                              FStar_SMTEncoding_Util.mkGT uu____8749 in
                            let uu____8754 =
                              let uu____8756 =
                                let uu____8757 =
                                  let uu____8760 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8761 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8760, uu____8761) in
                                FStar_SMTEncoding_Util.mkGTE uu____8757 in
                              let uu____8762 =
                                let uu____8764 =
                                  let uu____8765 =
                                    let uu____8768 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8769 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8768, uu____8769) in
                                  FStar_SMTEncoding_Util.mkLT uu____8765 in
                                [uu____8764] in
                              uu____8756 :: uu____8762 in
                            uu____8748 :: uu____8754 in
                          typing_pred_y :: uu____8746 in
                        typing_pred :: uu____8744 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8742 in
                    (uu____8741, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8738 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8737) in
              mkForall_fuel uu____8731 in
            (uu____8730, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Term.Assume uu____8726 in
        [uu____8725] in
      uu____8694 :: uu____8723 in
    uu____8660 :: uu____8692 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8799 =
      let uu____8800 =
        let uu____8804 =
          let uu____8805 =
            let uu____8811 =
              let uu____8814 =
                let uu____8816 = FStar_SMTEncoding_Term.boxString b in
                [uu____8816] in
              [uu____8814] in
            let uu____8819 =
              let uu____8820 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8820 tt in
            (uu____8811, [bb], uu____8819) in
          FStar_SMTEncoding_Util.mkForall uu____8805 in
        (uu____8804, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Term.Assume uu____8800 in
    let uu____8831 =
      let uu____8833 =
        let uu____8834 =
          let uu____8838 =
            let uu____8839 =
              let uu____8845 =
                let uu____8846 =
                  let uu____8849 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8849) in
                FStar_SMTEncoding_Util.mkImp uu____8846 in
              ([[typing_pred]], [xx], uu____8845) in
            mkForall_fuel uu____8839 in
          (uu____8838, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8834 in
      [uu____8833] in
    uu____8799 :: uu____8831 in
  let mk_ref1 env reft_name uu____8871 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8882 =
        let uu____8886 =
          let uu____8888 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8888] in
        (reft_name, uu____8886) in
      FStar_SMTEncoding_Util.mkApp uu____8882 in
    let refb =
      let uu____8891 =
        let uu____8895 =
          let uu____8897 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8897] in
        (reft_name, uu____8895) in
      FStar_SMTEncoding_Util.mkApp uu____8891 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8901 =
      let uu____8902 =
        let uu____8906 =
          let uu____8907 =
            let uu____8913 =
              let uu____8914 =
                let uu____8917 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8917) in
              FStar_SMTEncoding_Util.mkImp uu____8914 in
            ([[typing_pred]], [xx; aa], uu____8913) in
          mkForall_fuel uu____8907 in
        (uu____8906, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Term.Assume uu____8902 in
    let uu____8932 =
      let uu____8934 =
        let uu____8935 =
          let uu____8939 =
            let uu____8940 =
              let uu____8946 =
                let uu____8947 =
                  let uu____8950 =
                    FStar_SMTEncoding_Util.mkAnd (typing_pred, typing_pred_b) in
                  let uu____8951 =
                    let uu____8952 =
                      let uu____8955 = FStar_SMTEncoding_Util.mkFreeV aa in
                      let uu____8956 = FStar_SMTEncoding_Util.mkFreeV bb in
                      (uu____8955, uu____8956) in
                    FStar_SMTEncoding_Util.mkEq uu____8952 in
                  (uu____8950, uu____8951) in
                FStar_SMTEncoding_Util.mkImp uu____8947 in
              ([[typing_pred; typing_pred_b]], [xx; aa; bb], uu____8946) in
            mkForall_fuel' (Prims.parse_int "2") uu____8940 in
          (uu____8939, (Some "ref typing is injective"), "ref_injectivity") in
        FStar_SMTEncoding_Term.Assume uu____8935 in
      [uu____8934] in
    uu____8901 :: uu____8932 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8998 =
      let uu____8999 =
        let uu____9003 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9003, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Term.Assume uu____8999 in
    [uu____8998] in
  let mk_and_interp env conj uu____9014 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9024 =
        let uu____9028 =
          let uu____9030 = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
          [uu____9030] in
        ("Valid", uu____9028) in
      FStar_SMTEncoding_Util.mkApp uu____9024 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9037 =
      let uu____9038 =
        let uu____9042 =
          let uu____9043 =
            let uu____9049 =
              let uu____9050 =
                let uu____9053 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9053, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9050 in
            ([[valid]], [aa; bb], uu____9049) in
          FStar_SMTEncoding_Util.mkForall uu____9043 in
        (uu____9042, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Term.Assume uu____9038 in
    [uu____9037] in
  let mk_or_interp env disj uu____9077 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9087 =
        let uu____9091 =
          let uu____9093 = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
          [uu____9093] in
        ("Valid", uu____9091) in
      FStar_SMTEncoding_Util.mkApp uu____9087 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9100 =
      let uu____9101 =
        let uu____9105 =
          let uu____9106 =
            let uu____9112 =
              let uu____9113 =
                let uu____9116 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9116, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9113 in
            ([[valid]], [aa; bb], uu____9112) in
          FStar_SMTEncoding_Util.mkForall uu____9106 in
        (uu____9105, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Term.Assume uu____9101 in
    [uu____9100] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let valid =
      let uu____9154 =
        let uu____9158 =
          let uu____9160 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
          [uu____9160] in
        ("Valid", uu____9158) in
      FStar_SMTEncoding_Util.mkApp uu____9154 in
    let uu____9163 =
      let uu____9164 =
        let uu____9168 =
          let uu____9169 =
            let uu____9175 =
              let uu____9176 =
                let uu____9179 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9179, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9176 in
            ([[valid]], [aa; xx1; yy1], uu____9175) in
          FStar_SMTEncoding_Util.mkForall uu____9169 in
        (uu____9168, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Term.Assume uu____9164 in
    [uu____9163] in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let valid =
      let uu____9223 =
        let uu____9227 =
          let uu____9229 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
          [uu____9229] in
        ("Valid", uu____9227) in
      FStar_SMTEncoding_Util.mkApp uu____9223 in
    let uu____9232 =
      let uu____9233 =
        let uu____9237 =
          let uu____9238 =
            let uu____9244 =
              let uu____9245 =
                let uu____9248 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9248, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9245 in
            ([[valid]], [aa; bb; xx1; yy1], uu____9244) in
          FStar_SMTEncoding_Util.mkForall uu____9238 in
        (uu____9237, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Term.Assume uu____9233 in
    [uu____9232] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9286 =
        let uu____9290 =
          let uu____9292 = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
          [uu____9292] in
        ("Valid", uu____9290) in
      FStar_SMTEncoding_Util.mkApp uu____9286 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9299 =
      let uu____9300 =
        let uu____9304 =
          let uu____9305 =
            let uu____9311 =
              let uu____9312 =
                let uu____9315 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9315, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9312 in
            ([[valid]], [aa; bb], uu____9311) in
          FStar_SMTEncoding_Util.mkForall uu____9305 in
        (uu____9304, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Term.Assume uu____9300 in
    [uu____9299] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9349 =
        let uu____9353 =
          let uu____9355 = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
          [uu____9355] in
        ("Valid", uu____9353) in
      FStar_SMTEncoding_Util.mkApp uu____9349 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9362 =
      let uu____9363 =
        let uu____9367 =
          let uu____9368 =
            let uu____9374 =
              let uu____9375 =
                let uu____9378 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9378, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9375 in
            ([[valid]], [aa; bb], uu____9374) in
          FStar_SMTEncoding_Util.mkForall uu____9368 in
        (uu____9367, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Term.Assume uu____9363 in
    [uu____9362] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let valid =
      let uu____9408 =
        let uu____9412 =
          let uu____9414 = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
          [uu____9414] in
        ("Valid", uu____9412) in
      FStar_SMTEncoding_Util.mkApp uu____9408 in
    let not_valid_a =
      let uu____9418 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9418 in
    let uu____9420 =
      let uu____9421 =
        let uu____9425 =
          let uu____9426 =
            let uu____9432 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[valid]], [aa], uu____9432) in
          FStar_SMTEncoding_Util.mkForall uu____9426 in
        (uu____9425, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Term.Assume uu____9421 in
    [uu____9420] in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let valid =
      let uu____9468 =
        let uu____9472 =
          let uu____9474 = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b]) in
          [uu____9474] in
        ("Valid", uu____9472) in
      FStar_SMTEncoding_Util.mkApp uu____9468 in
    let valid_b_x =
      let uu____9478 =
        let uu____9482 =
          let uu____9484 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9484] in
        ("Valid", uu____9482) in
      FStar_SMTEncoding_Util.mkApp uu____9478 in
    let uu____9486 =
      let uu____9487 =
        let uu____9491 =
          let uu____9492 =
            let uu____9498 =
              let uu____9499 =
                let uu____9502 =
                  let uu____9503 =
                    let uu____9509 =
                      let uu____9512 =
                        let uu____9514 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9514] in
                      [uu____9512] in
                    let uu____9517 =
                      let uu____9518 =
                        let uu____9521 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9521, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9518 in
                    (uu____9509, [xx1], uu____9517) in
                  FStar_SMTEncoding_Util.mkForall uu____9503 in
                (uu____9502, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9499 in
            ([[valid]], [aa; bb], uu____9498) in
          FStar_SMTEncoding_Util.mkForall uu____9492 in
        (uu____9491, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Term.Assume uu____9487 in
    [uu____9486] in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let valid =
      let uu____9568 =
        let uu____9572 =
          let uu____9574 = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b]) in
          [uu____9574] in
        ("Valid", uu____9572) in
      FStar_SMTEncoding_Util.mkApp uu____9568 in
    let valid_b_x =
      let uu____9578 =
        let uu____9582 =
          let uu____9584 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9584] in
        ("Valid", uu____9582) in
      FStar_SMTEncoding_Util.mkApp uu____9578 in
    let uu____9586 =
      let uu____9587 =
        let uu____9591 =
          let uu____9592 =
            let uu____9598 =
              let uu____9599 =
                let uu____9602 =
                  let uu____9603 =
                    let uu____9609 =
                      let uu____9612 =
                        let uu____9614 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9614] in
                      [uu____9612] in
                    let uu____9617 =
                      let uu____9618 =
                        let uu____9621 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9621, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9618 in
                    (uu____9609, [xx1], uu____9617) in
                  FStar_SMTEncoding_Util.mkExists uu____9603 in
                (uu____9602, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9599 in
            ([[valid]], [aa; bb], uu____9598) in
          FStar_SMTEncoding_Util.mkForall uu____9592 in
        (uu____9591, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Term.Assume uu____9587 in
    [uu____9586] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9657 =
      let uu____9658 =
        let uu____9662 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9663 = varops.mk_unique "typing_range_const" in
        (uu____9662, (Some "Range_const typing"), uu____9663) in
      FStar_SMTEncoding_Term.Assume uu____9658 in
    [uu____9657] in
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
          let uu____9925 =
            FStar_Util.find_opt
              (fun uu____9943  ->
                 match uu____9943 with
                 | (l,uu____9953) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9925 with
          | None  -> []
          | Some (uu____9975,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10012 = encode_function_type_as_formula None None t env in
        match uu____10012 with
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
            let uu____10044 =
              (let uu____10045 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10045) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10044
            then
              let uu____10049 = new_term_constant_and_tok_from_lid env lid in
              match uu____10049 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10061 =
                      let uu____10062 = FStar_Syntax_Subst.compress t_norm in
                      uu____10062.FStar_Syntax_Syntax.n in
                    match uu____10061 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10067) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10084  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10087 -> [] in
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
              (let uu____10096 = prims.is lid in
               if uu____10096
               then
                 let vname = varops.new_fvar lid in
                 let uu____10101 = prims.mk lid vname in
                 match uu____10101 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10116 =
                    let uu____10122 = curried_arrow_formals_comp t_norm in
                    match uu____10122 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10133 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10133
                          then
                            let uu____10134 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___153_10135 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___153_10135.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___153_10135.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___153_10135.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___153_10135.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___153_10135.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___153_10135.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___153_10135.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___153_10135.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___153_10135.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___153_10135.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___153_10135.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___153_10135.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___153_10135.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___153_10135.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___153_10135.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___153_10135.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___153_10135.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___153_10135.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___153_10135.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___153_10135.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___153_10135.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___153_10135.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___153_10135.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10134
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10142 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10142)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10116 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10169 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10169 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10182 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___124_10206  ->
                                     match uu___124_10206 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10209 =
                                           FStar_Util.prefix vars in
                                         (match uu____10209 with
                                          | (uu____10220,(xxsym,uu____10222))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10232 =
                                                let uu____10233 =
                                                  let uu____10237 =
                                                    let uu____10238 =
                                                      let uu____10244 =
                                                        let uu____10245 =
                                                          let uu____10248 =
                                                            let uu____10249 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10249 in
                                                          (vapp, uu____10248) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10245 in
                                                      ([[vapp]], vars,
                                                        uu____10244) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10238 in
                                                  (uu____10237,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10233 in
                                              [uu____10232])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10260 =
                                           FStar_Util.prefix vars in
                                         (match uu____10260 with
                                          | (uu____10271,(xxsym,uu____10273))
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
                                              let uu____10287 =
                                                let uu____10288 =
                                                  let uu____10292 =
                                                    let uu____10293 =
                                                      let uu____10299 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10299) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10293 in
                                                  (uu____10292,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10288 in
                                              [uu____10287])
                                     | uu____10308 -> [])) in
                           let uu____10309 = encode_binders None formals env1 in
                           (match uu____10309 with
                            | (vars,guards,env',decls1,uu____10325) ->
                                let uu____10332 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10337 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10337, decls1)
                                  | Some p ->
                                      let uu____10339 = encode_formula p env' in
                                      (match uu____10339 with
                                       | (g,ds) ->
                                           let uu____10346 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10346,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10332 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10355 =
                                         let uu____10359 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10359) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10355 in
                                     let uu____10364 =
                                       let vname_decl =
                                         let uu____10369 =
                                           let uu____10375 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10380  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10375,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10369 in
                                       let uu____10385 =
                                         let env2 =
                                           let uu___154_10389 = env1 in
                                           {
                                             bindings =
                                               (uu___154_10389.bindings);
                                             depth = (uu___154_10389.depth);
                                             tcenv = (uu___154_10389.tcenv);
                                             warn = (uu___154_10389.warn);
                                             cache = (uu___154_10389.cache);
                                             nolabels =
                                               (uu___154_10389.nolabels);
                                             use_zfuel_name =
                                               (uu___154_10389.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___154_10389.current_module_name)
                                           } in
                                         let uu____10390 =
                                           let uu____10391 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10391 in
                                         if uu____10390
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10385 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10401::uu____10402 ->
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
                                                   let uu____10425 =
                                                     let uu____10431 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10431) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10425 in
                                                 FStar_SMTEncoding_Term.Assume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10445 ->
                                                 FStar_SMTEncoding_Term.Assume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10447 =
                                             match formals with
                                             | [] ->
                                                 let uu____10456 =
                                                   let uu____10457 =
                                                     let uu____10459 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10459 in
                                                   push_free_var env1 lid
                                                     vname uu____10457 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10456)
                                             | uu____10462 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10467 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10467 in
                                                 let name_tok_corr =
                                                   let uu____10469 =
                                                     let uu____10473 =
                                                       let uu____10474 =
                                                         let uu____10480 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10480) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10474 in
                                                     (uu____10473,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Term.Assume
                                                     uu____10469 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10447 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10364 with
                                      | (decls2,env2) ->
                                          let uu____10504 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10509 =
                                              encode_term res_t1 env' in
                                            match uu____10509 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10517 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10517,
                                                  decls) in
                                          (match uu____10504 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10525 =
                                                   let uu____10529 =
                                                     let uu____10530 =
                                                       let uu____10536 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10536) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10530 in
                                                   (uu____10529,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____10525 in
                                               let freshness =
                                                 let uu____10545 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10545
                                                 then
                                                   let uu____10548 =
                                                     let uu____10549 =
                                                       let uu____10555 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10561 =
                                                         varops.next_id () in
                                                       (vname, uu____10555,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10561) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10549 in
                                                   let uu____10563 =
                                                     let uu____10565 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10565] in
                                                   uu____10548 :: uu____10563
                                                 else [] in
                                               let g =
                                                 let uu____10569 =
                                                   let uu____10571 =
                                                     let uu____10573 =
                                                       let uu____10575 =
                                                         let uu____10577 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10577 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10575 in
                                                     FStar_List.append decls3
                                                       uu____10573 in
                                                   FStar_List.append decls2
                                                     uu____10571 in
                                                 FStar_List.append decls11
                                                   uu____10569 in
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
          let uu____10599 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10599 with
          | None  ->
              let uu____10622 = encode_free_var env x t t_norm [] in
              (match uu____10622 with
               | (decls,env1) ->
                   let uu____10637 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10637 with
                    | (n1,x',uu____10656) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10668) -> ((n1, x1), [], env)
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
          let uu____10701 = encode_free_var env lid t tt quals in
          match uu____10701 with
          | (decls,env1) ->
              let uu____10712 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10712
              then
                let uu____10716 =
                  let uu____10718 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10718 in
                (uu____10716, env1)
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
             (fun uu____10746  ->
                fun lb  ->
                  match uu____10746 with
                  | (decls,env1) ->
                      let uu____10758 =
                        let uu____10762 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10762
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10758 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10776 = FStar_Syntax_Util.head_and_args t in
    match uu____10776 with
    | (hd1,args) ->
        let uu____10802 =
          let uu____10803 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10803.FStar_Syntax_Syntax.n in
        (match uu____10802 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10807,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10820 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10835  ->
      fun quals  ->
        match uu____10835 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10884 = FStar_Util.first_N nbinders formals in
              match uu____10884 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10924  ->
                         fun uu____10925  ->
                           match (uu____10924, uu____10925) with
                           | ((formal,uu____10935),(binder,uu____10937)) ->
                               let uu____10942 =
                                 let uu____10947 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10947) in
                               FStar_Syntax_Syntax.NT uu____10942) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10952 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10966  ->
                              match uu____10966 with
                              | (x,i) ->
                                  let uu____10973 =
                                    let uu___155_10974 = x in
                                    let uu____10975 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___155_10974.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___155_10974.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10975
                                    } in
                                  (uu____10973, i))) in
                    FStar_All.pipe_right uu____10952
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10987 =
                      let uu____10989 =
                        let uu____10990 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10990.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10989 in
                    let uu____10994 =
                      let uu____10995 = FStar_Syntax_Subst.compress body in
                      let uu____10996 =
                        let uu____10997 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10997 in
                      FStar_Syntax_Syntax.extend_app_n uu____10995
                        uu____10996 in
                    uu____10994 uu____10987 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11039 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11039
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___156_11040 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___156_11040.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___156_11040.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___156_11040.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___156_11040.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___156_11040.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___156_11040.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___156_11040.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___156_11040.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___156_11040.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___156_11040.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___156_11040.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___156_11040.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___156_11040.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___156_11040.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___156_11040.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___156_11040.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___156_11040.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___156_11040.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___156_11040.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___156_11040.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___156_11040.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___156_11040.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___156_11040.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11061 = FStar_Syntax_Util.abs_formals e in
                match uu____11061 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11110::uu____11111 ->
                         let uu____11119 =
                           let uu____11120 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11120.FStar_Syntax_Syntax.n in
                         (match uu____11119 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11147 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11147 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11173 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11173
                                   then
                                     let uu____11191 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11191 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11237  ->
                                                   fun uu____11238  ->
                                                     match (uu____11237,
                                                             uu____11238)
                                                     with
                                                     | ((x,uu____11248),
                                                        (b,uu____11250)) ->
                                                         let uu____11255 =
                                                           let uu____11260 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11260) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11255)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11262 =
                                            let uu____11273 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11273) in
                                          (uu____11262, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11308 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11308 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11360) ->
                              let uu____11365 =
                                let uu____11376 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11376 in
                              (uu____11365, true)
                          | uu____11409 when Prims.op_Negation norm1 ->
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
                          | uu____11411 ->
                              let uu____11412 =
                                let uu____11413 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11414 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11413
                                  uu____11414 in
                              failwith uu____11412)
                     | uu____11427 ->
                         let uu____11428 =
                           let uu____11429 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11429.FStar_Syntax_Syntax.n in
                         (match uu____11428 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11456 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11456 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11474 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11474 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11522 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11550 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11550
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11557 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11598  ->
                            fun lb  ->
                              match uu____11598 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11649 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11649
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11652 =
                                      let uu____11660 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11660
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11652 with
                                    | (tok,decl,env2) ->
                                        let uu____11685 =
                                          let uu____11692 =
                                            let uu____11698 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11698, tok) in
                                          uu____11692 :: toks in
                                        (uu____11685, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11557 with
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
                        | uu____11800 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11805 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11805 vars)
                            else
                              (let uu____11807 =
                                 let uu____11811 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11811) in
                               FStar_SMTEncoding_Util.mkApp uu____11807) in
                      let uu____11816 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___125_11818  ->
                                 match uu___125_11818 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11819 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11822 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11822))) in
                      if uu____11816
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11842;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11844;
                                FStar_Syntax_Syntax.lbeff = uu____11845;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11886 =
                                 FStar_Syntax_Subst.univ_var_opening uvs in
                               (match uu____11886 with
                                | (univ_subst,univ_vars1) ->
                                    let env' =
                                      let uu___159_11901 = env1 in
                                      let uu____11902 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1.tcenv univ_vars1 in
                                      {
                                        bindings = (uu___159_11901.bindings);
                                        depth = (uu___159_11901.depth);
                                        tcenv = uu____11902;
                                        warn = (uu___159_11901.warn);
                                        cache = (uu___159_11901.cache);
                                        nolabels = (uu___159_11901.nolabels);
                                        use_zfuel_name =
                                          (uu___159_11901.use_zfuel_name);
                                        encode_non_total_function_typ =
                                          (uu___159_11901.encode_non_total_function_typ);
                                        current_module_name =
                                          (uu___159_11901.current_module_name)
                                      } in
                                    let t_norm1 =
                                      FStar_Syntax_Subst.subst univ_subst
                                        t_norm in
                                    let e1 =
                                      let uu____11905 =
                                        FStar_Syntax_Subst.subst univ_subst e in
                                      FStar_Syntax_Subst.compress uu____11905 in
                                    let uu____11906 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11906 with
                                     | ((binders,body,uu____11918,uu____11919),curry)
                                         ->
                                         ((let uu____11926 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11926
                                           then
                                             let uu____11927 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11928 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11927 uu____11928
                                           else ());
                                          (let uu____11930 =
                                             encode_binders None binders env' in
                                           match uu____11930 with
                                           | (vars,guards,env'1,binder_decls,uu____11946)
                                               ->
                                               let body1 =
                                                 let uu____11954 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11954
                                                 then
                                                   reify_body env'1.tcenv
                                                     body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11957 =
                                                 let uu____11962 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11962
                                                 then
                                                   let uu____11968 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11969 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11968, uu____11969)
                                                 else
                                                   (let uu____11975 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11975)) in
                                               (match uu____11957 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11989 =
                                                        let uu____11993 =
                                                          let uu____11994 =
                                                            let uu____12000 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12000) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11994 in
                                                        let uu____12006 =
                                                          let uu____12008 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12008 in
                                                        (uu____11993,
                                                          uu____12006,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Term.Assume
                                                        uu____11989 in
                                                    let uu____12010 =
                                                      let uu____12012 =
                                                        let uu____12014 =
                                                          let uu____12016 =
                                                            let uu____12018 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12018 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12016 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12014 in
                                                      FStar_List.append
                                                        decls1 uu____12012 in
                                                    (uu____12010, env1))))))
                           | uu____12021 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12040 = varops.fresh "fuel" in
                             (uu____12040, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12043 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12082  ->
                                     fun uu____12083  ->
                                       match (uu____12082, uu____12083) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12165 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12165 in
                                           let gtok =
                                             let uu____12167 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12167 in
                                           let env3 =
                                             let uu____12169 =
                                               let uu____12171 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12171 in
                                             push_free_var env2 flid gtok
                                               uu____12169 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12043 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12255
                                 t_norm uu____12257 =
                                 match (uu____12255, uu____12257) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12282;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12283;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12300 =
                                       FStar_Syntax_Subst.univ_var_opening
                                         uvs in
                                     (match uu____12300 with
                                      | (univ_subst,univ_vars1) ->
                                          let env' =
                                            let uu___160_12317 = env2 in
                                            let uu____12318 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env2.tcenv univ_vars1 in
                                            {
                                              bindings =
                                                (uu___160_12317.bindings);
                                              depth = (uu___160_12317.depth);
                                              tcenv = uu____12318;
                                              warn = (uu___160_12317.warn);
                                              cache = (uu___160_12317.cache);
                                              nolabels =
                                                (uu___160_12317.nolabels);
                                              use_zfuel_name =
                                                (uu___160_12317.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___160_12317.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___160_12317.current_module_name)
                                            } in
                                          let t_norm1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst t_norm in
                                          let e1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst e in
                                          ((let uu____12322 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12322
                                            then
                                              let uu____12323 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12324 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12325 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12323 uu____12324
                                                uu____12325
                                            else ());
                                           (let uu____12327 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12327 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12349 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12349
                                                  then
                                                    let uu____12350 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12351 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12352 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12353 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12350 uu____12351
                                                      uu____12352 uu____12353
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12357 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12357 with
                                                  | (vars,guards,env'1,binder_decls,uu____12375)
                                                      ->
                                                      let decl_g =
                                                        let uu____12383 =
                                                          let uu____12389 =
                                                            let uu____12391 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12391 in
                                                          (g, uu____12389,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12383 in
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
                                                        let uu____12406 =
                                                          let uu____12410 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12410) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12406 in
                                                      let gsapp =
                                                        let uu____12416 =
                                                          let uu____12420 =
                                                            let uu____12422 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12422 ::
                                                              vars_tm in
                                                          (g, uu____12420) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12416 in
                                                      let gmax =
                                                        let uu____12426 =
                                                          let uu____12430 =
                                                            let uu____12432 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12432 ::
                                                              vars_tm in
                                                          (g, uu____12430) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12426 in
                                                      let body1 =
                                                        let uu____12436 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12436
                                                        then
                                                          reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12438 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12438 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12449
                                                               =
                                                               let uu____12453
                                                                 =
                                                                 let uu____12454
                                                                   =
                                                                   let uu____12462
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
                                                                    uu____12462) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12454 in
                                                               let uu____12473
                                                                 =
                                                                 let uu____12475
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12475 in
                                                               (uu____12453,
                                                                 uu____12473,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12449 in
                                                           let eqn_f =
                                                             let uu____12478
                                                               =
                                                               let uu____12482
                                                                 =
                                                                 let uu____12483
                                                                   =
                                                                   let uu____12489
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12489) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12483 in
                                                               (uu____12482,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12478 in
                                                           let eqn_g' =
                                                             let uu____12497
                                                               =
                                                               let uu____12501
                                                                 =
                                                                 let uu____12502
                                                                   =
                                                                   let uu____12508
                                                                    =
                                                                    let uu____12509
                                                                    =
                                                                    let uu____12512
                                                                    =
                                                                    let uu____12513
                                                                    =
                                                                    let uu____12517
                                                                    =
                                                                    let uu____12519
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12519
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12517) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12513 in
                                                                    (gsapp,
                                                                    uu____12512) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12509 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12508) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12502 in
                                                               (uu____12501,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12497 in
                                                           let uu____12531 =
                                                             let uu____12536
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12536
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12553)
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
                                                                    let uu____12568
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12568
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12571
                                                                    =
                                                                    let uu____12575
                                                                    =
                                                                    let uu____12576
                                                                    =
                                                                    let uu____12582
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12582) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12576 in
                                                                    (uu____12575,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Term.Assume
                                                                    uu____12571 in
                                                                 let uu____12593
                                                                   =
                                                                   let uu____12597
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12597
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12605
                                                                    =
                                                                    let uu____12607
                                                                    =
                                                                    let uu____12608
                                                                    =
                                                                    let uu____12612
                                                                    =
                                                                    let uu____12613
                                                                    =
                                                                    let uu____12619
                                                                    =
                                                                    let uu____12620
                                                                    =
                                                                    let uu____12623
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12623,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12620 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12619) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12613 in
                                                                    (uu____12612,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12608 in
                                                                    [uu____12607] in
                                                                    (d3,
                                                                    uu____12605) in
                                                                 (match uu____12593
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12531
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
                               let uu____12658 =
                                 let uu____12665 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12697  ->
                                      fun uu____12698  ->
                                        match (uu____12697, uu____12698) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12774 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12774 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12665 in
                               (match uu____12658 with
                                | (decls2,eqns,env01) ->
                                    let uu____12814 =
                                      let isDeclFun uu___126_12822 =
                                        match uu___126_12822 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12823 -> true
                                        | uu____12829 -> false in
                                      let uu____12830 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12830
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12814 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12857 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12857
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
      (let uu____12890 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____12890
       then
         let uu____12891 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
           uu____12891
       else ());
      (let nm =
         let uu____12894 = FStar_Syntax_Util.lid_of_sigelt se in
         match uu____12894 with | None  -> "" | Some l -> l.FStar_Ident.str in
       let uu____12897 = encode_sigelt' env se in
       match uu____12897 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12906 =
                  let uu____12908 =
                    let uu____12909 = FStar_Util.format1 "<Skipped %s/>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12909 in
                  [uu____12908] in
                (uu____12906, e)
            | uu____12911 ->
                let uu____12912 =
                  let uu____12914 =
                    let uu____12916 =
                      let uu____12917 =
                        FStar_Util.format1 "<Start encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12917 in
                    uu____12916 :: g in
                  let uu____12918 =
                    let uu____12920 =
                      let uu____12921 =
                        FStar_Util.format1 "</end encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12921 in
                    [uu____12920] in
                  FStar_List.append uu____12914 uu____12918 in
                (uu____12912, e)))
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12929 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12938 =
            let uu____12939 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12939 Prims.op_Negation in
          if uu____12938
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12959 ->
                   let uu____12960 =
                     let uu____12963 =
                       let uu____12964 =
                         let uu____12979 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12979) in
                       FStar_Syntax_Syntax.Tm_abs uu____12964 in
                     FStar_Syntax_Syntax.mk uu____12963 in
                   uu____12960 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13032 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13032 with
               | (aname,atok,env2) ->
                   let uu____13042 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13042 with
                    | (formals,uu____13052) ->
                        let uu____13059 =
                          let uu____13062 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13062 env2 in
                        (match uu____13059 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13070 =
                                 let uu____13071 =
                                   let uu____13077 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13085  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13077,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13071 in
                               [uu____13070;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13092 =
                               let aux uu____13121 uu____13122 =
                                 match (uu____13121, uu____13122) with
                                 | ((bv,uu____13149),(env3,acc_sorts,acc)) ->
                                     let uu____13170 = gen_term_var env3 bv in
                                     (match uu____13170 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13092 with
                              | (uu____13208,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13222 =
                                      let uu____13226 =
                                        let uu____13227 =
                                          let uu____13233 =
                                            let uu____13234 =
                                              let uu____13237 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13237) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13234 in
                                          ([[app]], xs_sorts, uu____13233) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13227 in
                                      (uu____13226, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Term.Assume uu____13222 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13249 =
                                      let uu____13253 =
                                        let uu____13254 =
                                          let uu____13260 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13260) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13254 in
                                      (uu____13253,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Term.Assume uu____13249 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13270 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13270 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____13286,uu____13287,uu____13288) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13291 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13291 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13302,t,quals) ->
          let will_encode_definition =
            let uu____13308 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___127_13310  ->
                      match uu___127_13310 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13313 -> false)) in
            Prims.op_Negation uu____13308 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13319 = encode_top_level_val env fv t quals in
             match uu____13319 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13331 =
                   let uu____13333 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13333 in
                 (uu____13331, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____13338) ->
          let uu____13341 = encode_formula f env in
          (match uu____13341 with
           | (f1,decls) ->
               let g =
                 let uu____13350 =
                   let uu____13351 =
                     let uu____13355 =
                       let uu____13357 =
                         let uu____13358 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13358 in
                       Some uu____13357 in
                     let uu____13359 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13355, uu____13359) in
                   FStar_SMTEncoding_Term.Assume uu____13351 in
                 [uu____13350] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13363,quals,uu____13365) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13373 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13380 =
                       let uu____13385 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13385.FStar_Syntax_Syntax.fv_name in
                     uu____13380.FStar_Syntax_Syntax.v in
                   let uu____13389 =
                     let uu____13390 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13390 in
                   if uu____13389
                   then
                     let val_decl =
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp), quals));
                         FStar_Syntax_Syntax.sigrng =
                           (se.FStar_Syntax_Syntax.sigrng)
                       } in
                     let uu____13409 = encode_sigelt' env1 val_decl in
                     match uu____13409 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13373 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13426,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13428;
                          FStar_Syntax_Syntax.lbtyp = uu____13429;
                          FStar_Syntax_Syntax.lbeff = uu____13430;
                          FStar_Syntax_Syntax.lbdef = uu____13431;_}::[]),uu____13432,uu____13433,uu____13434)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13450 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13450 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let valid_b2t_x =
                 let uu____13468 =
                   let uu____13472 =
                     let uu____13474 =
                       FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
                     [uu____13474] in
                   ("Valid", uu____13472) in
                 FStar_SMTEncoding_Util.mkApp uu____13468 in
               let decls =
                 let uu____13479 =
                   let uu____13481 =
                     let uu____13482 =
                       let uu____13486 =
                         let uu____13487 =
                           let uu____13493 =
                             let uu____13494 =
                               let uu____13497 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13497) in
                             FStar_SMTEncoding_Util.mkEq uu____13494 in
                           ([[valid_b2t_x]], [xx], uu____13493) in
                         FStar_SMTEncoding_Util.mkForall uu____13487 in
                       (uu____13486, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Term.Assume uu____13482 in
                   [uu____13481] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13479 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let
          (uu____13514,uu____13515,quals,uu____13517) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___128_13525  ->
                  match uu___128_13525 with
                  | FStar_Syntax_Syntax.Discriminator uu____13526 -> true
                  | uu____13527 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13529,lids,quals,uu____13532) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13541 =
                     let uu____13542 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13542.FStar_Ident.idText in
                   uu____13541 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___129_13544  ->
                     match uu___129_13544 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13545 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13548,quals,uu____13550) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___130_13562  ->
                  match uu___130_13562 with
                  | FStar_Syntax_Syntax.Projector uu____13563 -> true
                  | uu____13566 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13573 = try_lookup_free_var env l in
          (match uu____13573 with
           | Some uu____13577 -> ([], env)
           | None  ->
               let se1 =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp), quals));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13586,quals,uu____13588) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13602,uu____13603) ->
          let uu____13610 = encode_signature env ses in
          (match uu____13610 with
           | (g,env1) ->
               let uu____13620 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___131_13630  ->
                         match uu___131_13630 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13631,Some "inversion axiom",uu____13632)
                             -> false
                         | uu____13634 -> true)) in
               (match uu____13620 with
                | (g',inversions) ->
                    let uu____13643 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___132_13653  ->
                              match uu___132_13653 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13654 ->
                                  true
                              | uu____13660 -> false)) in
                    (match uu____13643 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13671,tps,k,uu____13674,datas,quals) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___133_13685  ->
                    match uu___133_13685 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13686 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13693 = c in
              match uu____13693 with
              | (name,args,uu____13697,uu____13698,uu____13699) ->
                  let uu____13702 =
                    let uu____13703 =
                      let uu____13709 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13716  ->
                                match uu____13716 with
                                | (uu____13720,sort,uu____13722) -> sort)) in
                      (name, uu____13709, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13703 in
                  [uu____13702]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13740 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13743 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13743 FStar_Option.isNone)) in
            if uu____13740
            then []
            else
              (let uu____13760 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13760 with
               | (xxsym,xx) ->
                   let uu____13766 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13777  ->
                             fun l  ->
                               match uu____13777 with
                               | (out,decls) ->
                                   let uu____13789 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13789 with
                                    | (uu____13795,data_t) ->
                                        let uu____13797 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13797 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13826 =
                                                 let uu____13827 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13827.FStar_Syntax_Syntax.n in
                                               match uu____13826 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13835,indices) ->
                                                   indices
                                               | uu____13851 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13863  ->
                                                         match uu____13863
                                                         with
                                                         | (x,uu____13867) ->
                                                             let uu____13868
                                                               =
                                                               let uu____13869
                                                                 =
                                                                 let uu____13873
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13873,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13869 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13868)
                                                    env) in
                                             let uu____13875 =
                                               encode_args indices env1 in
                                             (match uu____13875 with
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
                                                      let uu____13895 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13903
                                                                 =
                                                                 let uu____13906
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13906,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13903)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13895
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13908 =
                                                      let uu____13909 =
                                                        let uu____13912 =
                                                          let uu____13913 =
                                                            let uu____13916 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13916,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13913 in
                                                        (out, uu____13912) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13909 in
                                                    (uu____13908,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13766 with
                    | (data_ax,decls) ->
                        let uu____13924 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13924 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13935 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13935 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13938 =
                                 let uu____13942 =
                                   let uu____13943 =
                                     let uu____13949 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13957 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13949,
                                       uu____13957) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13943 in
                                 let uu____13965 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13942, (Some "inversion axiom"),
                                   uu____13965) in
                               FStar_SMTEncoding_Term.Assume uu____13938 in
                             let pattern_guarded_inversion =
                               let uu____13969 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13969
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13977 =
                                   let uu____13978 =
                                     let uu____13982 =
                                       let uu____13983 =
                                         let uu____13989 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13997 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13989, uu____13997) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13983 in
                                     let uu____14005 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13982, (Some "inversion axiom"),
                                       uu____14005) in
                                   FStar_SMTEncoding_Term.Assume uu____13978 in
                                 [uu____13977]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14008 =
            let uu____14016 =
              let uu____14017 = FStar_Syntax_Subst.compress k in
              uu____14017.FStar_Syntax_Syntax.n in
            match uu____14016 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14046 -> (tps, k) in
          (match uu____14008 with
           | (formals,res) ->
               let uu____14061 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14061 with
                | (formals1,res1) ->
                    let uu____14068 = encode_binders None formals1 env in
                    (match uu____14068 with
                     | (vars,guards,env',binder_decls,uu____14083) ->
                         let uu____14090 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14090 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14103 =
                                  let uu____14107 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14107) in
                                FStar_SMTEncoding_Util.mkApp uu____14103 in
                              let uu____14112 =
                                let tname_decl =
                                  let uu____14118 =
                                    let uu____14119 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14134  ->
                                              match uu____14134 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14142 = varops.next_id () in
                                    (tname, uu____14119,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14142, false) in
                                  constructor_or_logic_type_decl uu____14118 in
                                let uu____14147 =
                                  match vars with
                                  | [] ->
                                      let uu____14154 =
                                        let uu____14155 =
                                          let uu____14157 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14157 in
                                        push_free_var env1 t tname
                                          uu____14155 in
                                      ([], uu____14154)
                                  | uu____14161 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14167 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14167 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14176 =
                                          let uu____14180 =
                                            let uu____14181 =
                                              let uu____14189 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14189) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14181 in
                                          (uu____14180,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____14176 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14147 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14112 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14212 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14212 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14226 =
                                               let uu____14227 =
                                                 let uu____14231 =
                                                   let uu____14232 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14232 in
                                                 (uu____14231,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14227 in
                                             [uu____14226]
                                           else [] in
                                         let uu____14235 =
                                           let uu____14237 =
                                             let uu____14239 =
                                               let uu____14240 =
                                                 let uu____14244 =
                                                   let uu____14245 =
                                                     let uu____14251 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14251) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14245 in
                                                 (uu____14244, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14240 in
                                             [uu____14239] in
                                           FStar_List.append karr uu____14237 in
                                         FStar_List.append decls1 uu____14235 in
                                   let aux =
                                     let uu____14260 =
                                       let uu____14262 =
                                         inversion_axioms tapp vars in
                                       let uu____14264 =
                                         let uu____14266 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14266] in
                                       FStar_List.append uu____14262
                                         uu____14264 in
                                     FStar_List.append kindingAx uu____14260 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14271,uu____14272,uu____14273,uu____14274,uu____14275,uu____14276)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14283,t,uu____14285,n_tps,quals,uu____14288) ->
          let uu____14293 = new_term_constant_and_tok_from_lid env d in
          (match uu____14293 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14304 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14304 with
                | (formals,t_res) ->
                    let uu____14326 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14326 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14335 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14335 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14373 =
                                            mk_term_projector_name d x in
                                          (uu____14373,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14375 =
                                  let uu____14385 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14385, true) in
                                FStar_All.pipe_right uu____14375
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
                              let uu____14407 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14407 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14415::uu____14416 ->
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
                                         let uu____14441 =
                                           let uu____14447 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14447) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14441
                                     | uu____14460 -> tok_typing in
                                   let uu____14465 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14465 with
                                    | (vars',guards',env'',decls_formals,uu____14480)
                                        ->
                                        let uu____14487 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14487 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14506 ->
                                                   let uu____14510 =
                                                     let uu____14511 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14511 in
                                                   [uu____14510] in
                                             let encode_elim uu____14518 =
                                               let uu____14519 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14519 with
                                               | (head1,args) ->
                                                   let uu____14548 =
                                                     let uu____14549 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14549.FStar_Syntax_Syntax.n in
                                                   (match uu____14548 with
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
                                                        let uu____14567 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14567
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
                                                                 | uu____14593
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14601
                                                                    =
                                                                    let uu____14602
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14602 in
                                                                    if
                                                                    uu____14601
                                                                    then
                                                                    let uu____14609
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14609]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14611
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14624
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14624
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14646
                                                                    =
                                                                    let uu____14650
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14650 in
                                                                    (match uu____14646
                                                                    with
                                                                    | 
                                                                    (uu____14657,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14663
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14663
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14665
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14665
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
                                                             (match uu____14611
                                                              with
                                                              | (uu____14673,arg_vars,elim_eqns_or_guards,uu____14676)
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
                                                                    let uu____14695
                                                                    =
                                                                    let uu____14699
                                                                    =
                                                                    let uu____14700
                                                                    =
                                                                    let uu____14706
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14712
                                                                    =
                                                                    let uu____14713
                                                                    =
                                                                    let uu____14716
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14716) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14713 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14706,
                                                                    uu____14712) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14700 in
                                                                    (uu____14699,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14695 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14729
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14729,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14731
                                                                    =
                                                                    let uu____14735
                                                                    =
                                                                    let uu____14736
                                                                    =
                                                                    let uu____14742
                                                                    =
                                                                    let uu____14745
                                                                    =
                                                                    let uu____14747
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14747] in
                                                                    [uu____14745] in
                                                                    let uu____14750
                                                                    =
                                                                    let uu____14751
                                                                    =
                                                                    let uu____14754
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14755
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14754,
                                                                    uu____14755) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14751 in
                                                                    (uu____14742,
                                                                    [x],
                                                                    uu____14750) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14736 in
                                                                    let uu____14765
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14735,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14765) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14731
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14770
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
                                                                    (let uu____14785
                                                                    =
                                                                    let uu____14786
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14786
                                                                    dapp1 in
                                                                    [uu____14785]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14770
                                                                    FStar_List.flatten in
                                                                    let uu____14790
                                                                    =
                                                                    let uu____14794
                                                                    =
                                                                    let uu____14795
                                                                    =
                                                                    let uu____14801
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14807
                                                                    =
                                                                    let uu____14808
                                                                    =
                                                                    let uu____14811
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14811) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14808 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14801,
                                                                    uu____14807) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14795 in
                                                                    (uu____14794,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14790) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14821 ->
                                                        ((let uu____14823 =
                                                            let uu____14824 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14825 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14824
                                                              uu____14825 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14823);
                                                         ([], []))) in
                                             let uu____14828 = encode_elim () in
                                             (match uu____14828 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14840 =
                                                      let uu____14842 =
                                                        let uu____14844 =
                                                          let uu____14846 =
                                                            let uu____14848 =
                                                              let uu____14849
                                                                =
                                                                let uu____14855
                                                                  =
                                                                  let uu____14857
                                                                    =
                                                                    let uu____14858
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14858 in
                                                                  Some
                                                                    uu____14857 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14855) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14849 in
                                                            [uu____14848] in
                                                          let uu____14861 =
                                                            let uu____14863 =
                                                              let uu____14865
                                                                =
                                                                let uu____14867
                                                                  =
                                                                  let uu____14869
                                                                    =
                                                                    let uu____14871
                                                                    =
                                                                    let uu____14873
                                                                    =
                                                                    let uu____14874
                                                                    =
                                                                    let uu____14878
                                                                    =
                                                                    let uu____14879
                                                                    =
                                                                    let uu____14885
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14885) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14879 in
                                                                    (uu____14878,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14874 in
                                                                    let uu____14892
                                                                    =
                                                                    let uu____14894
                                                                    =
                                                                    let uu____14895
                                                                    =
                                                                    let uu____14899
                                                                    =
                                                                    let uu____14900
                                                                    =
                                                                    let uu____14906
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14912
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14906,
                                                                    uu____14912) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14900 in
                                                                    (uu____14899,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14895 in
                                                                    [uu____14894] in
                                                                    uu____14873
                                                                    ::
                                                                    uu____14892 in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14871 in
                                                                  FStar_List.append
                                                                    uu____14869
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14867 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14865 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14863 in
                                                          FStar_List.append
                                                            uu____14846
                                                            uu____14861 in
                                                        FStar_List.append
                                                          decls3 uu____14844 in
                                                      FStar_List.append
                                                        decls2 uu____14842 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14840 in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))
and encode_signature:
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____14933  ->
              fun se  ->
                match uu____14933 with
                | (g,env1) ->
                    let uu____14945 = encode_sigelt env1 se in
                    (match uu____14945 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14981 =
        match uu____14981 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14999 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____15004 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15004
                   then
                     let uu____15005 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15006 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15007 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15005 uu____15006 uu____15007
                   else ());
                  (let uu____15009 = encode_term t1 env1 in
                   match uu____15009 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15019 =
                         let uu____15023 =
                           let uu____15024 =
                             let uu____15025 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15025
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15024 in
                         new_term_constant_from_string env1 x uu____15023 in
                       (match uu____15019 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15036 = FStar_Options.log_queries () in
                              if uu____15036
                              then
                                let uu____15038 =
                                  let uu____15039 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15040 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15041 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15039 uu____15040 uu____15041 in
                                Some uu____15038
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15052,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15061 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15061 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____15080 = encode_sigelt env1 se in
                 (match uu____15080 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15090 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15090 with | (uu____15102,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15147  ->
            match uu____15147 with
            | (l,uu____15154,uu____15155) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15176  ->
            match uu____15176 with
            | (l,uu____15184,uu____15185) ->
                let uu____15190 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____15191 =
                  let uu____15193 =
                    let uu____15194 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15194 in
                  [uu____15193] in
                uu____15190 :: uu____15191)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15205 =
      let uu____15207 =
        let uu____15208 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15220 =
          let uu____15221 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15221 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15208;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15220
        } in
      [uu____15207] in
    FStar_ST.write last_env uu____15205
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15231 = FStar_ST.read last_env in
      match uu____15231 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15237 ->
          let uu___161_15239 = e in
          let uu____15240 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___161_15239.bindings);
            depth = (uu___161_15239.depth);
            tcenv;
            warn = (uu___161_15239.warn);
            cache = (uu___161_15239.cache);
            nolabels = (uu___161_15239.nolabels);
            use_zfuel_name = (uu___161_15239.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___161_15239.encode_non_total_function_typ);
            current_module_name = uu____15240
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15244 = FStar_ST.read last_env in
    match uu____15244 with
    | [] -> failwith "Empty env stack"
    | uu____15249::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15257  ->
    let uu____15258 = FStar_ST.read last_env in
    match uu____15258 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___162_15279 = hd1 in
          {
            bindings = (uu___162_15279.bindings);
            depth = (uu___162_15279.depth);
            tcenv = (uu___162_15279.tcenv);
            warn = (uu___162_15279.warn);
            cache = refs;
            nolabels = (uu___162_15279.nolabels);
            use_zfuel_name = (uu___162_15279.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_15279.encode_non_total_function_typ);
            current_module_name = (uu___162_15279.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15285  ->
    let uu____15286 = FStar_ST.read last_env in
    match uu____15286 with
    | [] -> failwith "Popping an empty stack"
    | uu____15291::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15299  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15302  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15305  ->
    let uu____15306 = FStar_ST.read last_env in
    match uu____15306 with
    | hd1::uu____15312::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15318 -> failwith "Impossible"
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
let encode_sig:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____15363 = FStar_Options.log_queries () in
        if uu____15363
        then
          let uu____15365 =
            let uu____15366 =
              let uu____15367 =
                let uu____15368 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15368 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15367 in
            FStar_SMTEncoding_Term.Caption uu____15366 in
          uu____15365 :: decls
        else decls in
      let env =
        let uu____15375 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15375 tcenv in
      let uu____15376 = encode_sigelt env se in
      match uu____15376 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15382 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15382))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15393 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15393
       then
         let uu____15394 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15394
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let uu____15399 =
         encode_signature
           (let uu___163_15403 = env in
            {
              bindings = (uu___163_15403.bindings);
              depth = (uu___163_15403.depth);
              tcenv = (uu___163_15403.tcenv);
              warn = false;
              cache = (uu___163_15403.cache);
              nolabels = (uu___163_15403.nolabels);
              use_zfuel_name = (uu___163_15403.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___163_15403.encode_non_total_function_typ);
              current_module_name = (uu___163_15403.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15399 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15415 = FStar_Options.log_queries () in
             if uu____15415
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___164_15420 = env1 in
               {
                 bindings = (uu___164_15420.bindings);
                 depth = (uu___164_15420.depth);
                 tcenv = (uu___164_15420.tcenv);
                 warn = true;
                 cache = (uu___164_15420.cache);
                 nolabels = (uu___164_15420.nolabels);
                 use_zfuel_name = (uu___164_15420.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___164_15420.encode_non_total_function_typ);
                 current_module_name = (uu___164_15420.current_module_name)
               });
            (let uu____15422 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15422
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
        (let uu____15457 =
           let uu____15458 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15458.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15457);
        (let env =
           let uu____15460 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15460 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15467 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15488 = aux rest in
                 (match uu____15488 with
                  | (out,rest1) ->
                      let t =
                        let uu____15506 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15506 with
                        | Some uu____15510 ->
                            let uu____15511 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15511
                              x.FStar_Syntax_Syntax.sort
                        | uu____15512 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15515 =
                        let uu____15517 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___165_15518 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___165_15518.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___165_15518.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15517 :: out in
                      (uu____15515, rest1))
             | uu____15521 -> ([], bindings1) in
           let uu____15525 = aux bindings in
           match uu____15525 with
           | (closing,bindings1) ->
               let uu____15539 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15539, bindings1) in
         match uu____15467 with
         | (q1,bindings1) ->
             let uu____15552 =
               let uu____15555 =
                 FStar_List.filter
                   (fun uu___134_15557  ->
                      match uu___134_15557 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15558 ->
                          false
                      | uu____15562 -> true) bindings1 in
               encode_env_bindings env uu____15555 in
             (match uu____15552 with
              | (env_decls,env1) ->
                  ((let uu____15573 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15573
                    then
                      let uu____15574 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15574
                    else ());
                   (let uu____15576 = encode_formula q1 env1 in
                    match uu____15576 with
                    | (phi,qdecls) ->
                        let uu____15588 =
                          let uu____15591 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15591 phi in
                        (match uu____15588 with
                         | (labels,phi1) ->
                             let uu____15601 = encode_labels labels in
                             (match uu____15601 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15622 =
                                      let uu____15626 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15627 =
                                        varops.mk_unique "@query" in
                                      (uu____15626, (Some "query"),
                                        uu____15627) in
                                    FStar_SMTEncoding_Term.Assume uu____15622 in
                                  let suffix =
                                    let uu____15631 =
                                      let uu____15633 =
                                        let uu____15635 =
                                          FStar_Options.print_z3_statistics
                                            () in
                                        if uu____15635
                                        then
                                          [FStar_SMTEncoding_Term.PrintStats]
                                        else [] in
                                      FStar_List.append uu____15633
                                        [FStar_SMTEncoding_Term.Echo "Done!"] in
                                    FStar_List.append label_suffix
                                      uu____15631 in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15647 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15647 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15649 = encode_formula q env in
       match uu____15649 with
       | (f,uu____15653) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15655) -> true
             | uu____15658 -> false)))