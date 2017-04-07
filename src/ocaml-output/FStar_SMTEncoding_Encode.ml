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
                                    let encoding =
                                      let uu____2907 =
                                        let uu____2910 =
                                          FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                            (Some fterm) xtm base_t in
                                        (uu____2910, refinement) in
                                      FStar_SMTEncoding_Util.mkAnd uu____2907 in
                                    let cvars =
                                      let uu____2915 =
                                        FStar_SMTEncoding_Term.free_variables
                                          encoding in
                                      FStar_All.pipe_right uu____2915
                                        (FStar_List.filter
                                           (fun uu____2921  ->
                                              match uu____2921 with
                                              | (y,uu____2925) ->
                                                  (y <> x1) && (y <> fsym))) in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort) in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort) in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars), encoding) in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey in
                                    let uu____2944 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2944 with
                                     | Some (t1,uu____2959,uu____2960) ->
                                         let uu____2970 =
                                           let uu____2971 =
                                             let uu____2975 =
                                               FStar_All.pipe_right cvars
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             (t1, uu____2975) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2971 in
                                         (uu____2970, [])
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____2992 =
                                             let uu____2993 =
                                               let uu____2994 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____2994 in
                                             Prims.strcat module_name
                                               uu____2993 in
                                           varops.mk_unique uu____2992 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3003 =
                                             let uu____3007 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars in
                                             (tsym, uu____3007) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3003 in
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
                                           let uu____3017 =
                                             let uu____3021 =
                                               let uu____3022 =
                                                 let uu____3028 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars,
                                                   uu____3028) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3022 in
                                             (uu____3021,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3017 in
                                         let t_kinding =
                                           let uu____3038 =
                                             let uu____3042 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars,
                                                   t_has_kind) in
                                             (uu____3042,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3038 in
                                         let t_interp =
                                           let uu____3052 =
                                             let uu____3056 =
                                               let uu____3057 =
                                                 let uu____3063 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars), uu____3063) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3057 in
                                             let uu____3075 =
                                               let uu____3077 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3077 in
                                             (uu____3056, uu____3075,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3052 in
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
             let uu____3105 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3105 in
           let uu____3109 = encode_term_pred None k env ttm in
           (match uu____3109 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3117 =
                    let uu____3121 =
                      let uu____3122 =
                        let uu____3123 =
                          let uu____3124 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3124 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3123 in
                      varops.mk_unique uu____3122 in
                    (t_has_k, (Some "Uvar typing"), uu____3121) in
                  FStar_SMTEncoding_Term.Assume uu____3117 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3130 ->
           let uu____3140 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3140 with
            | (head1,args_e) ->
                let uu____3168 =
                  let uu____3176 =
                    let uu____3177 = FStar_Syntax_Subst.compress head1 in
                    uu____3177.FStar_Syntax_Syntax.n in
                  (uu____3176, args_e) in
                (match uu____3168 with
                 | (uu____3187,uu____3188) when head_redex env head1 ->
                     let uu____3199 = whnf env t in
                     encode_term uu____3199 env
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
                     let uu____3273 = encode_term v1 env in
                     (match uu____3273 with
                      | (v11,decls1) ->
                          let uu____3280 = encode_term v2 env in
                          (match uu____3280 with
                           | (v21,decls2) ->
                               let uu____3287 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3287,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3289) ->
                     let e0 =
                       let uu____3303 =
                         let uu____3306 =
                           let uu____3307 =
                             let uu____3317 =
                               let uu____3323 = FStar_List.hd args_e in
                               [uu____3323] in
                             (head1, uu____3317) in
                           FStar_Syntax_Syntax.Tm_app uu____3307 in
                         FStar_Syntax_Syntax.mk uu____3306 in
                       uu____3303 None head1.FStar_Syntax_Syntax.pos in
                     ((let uu____3356 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3356
                       then
                         let uu____3357 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Trying to normalize %s\n"
                           uu____3357
                       else ());
                      (let e01 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Reify;
                           FStar_TypeChecker_Normalize.Eager_unfolding;
                           FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                           env.tcenv e0 in
                       (let uu____3361 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify") in
                        if uu____3361
                        then
                          let uu____3362 =
                            FStar_Syntax_Print.term_to_string e01 in
                          FStar_Util.print1 "Result of normalization %s\n"
                            uu____3362
                        else ());
                       (let e02 =
                          let uu____3365 =
                            let uu____3366 =
                              let uu____3367 =
                                FStar_Syntax_Subst.compress e01 in
                              uu____3367.FStar_Syntax_Syntax.n in
                            match uu____3366 with
                            | FStar_Syntax_Syntax.Tm_app uu____3370 -> false
                            | uu____3380 -> true in
                          if uu____3365
                          then e01
                          else
                            (let uu____3382 =
                               FStar_Syntax_Util.head_and_args e01 in
                             match uu____3382 with
                             | (head2,args) ->
                                 let uu____3408 =
                                   let uu____3409 =
                                     let uu____3410 =
                                       FStar_Syntax_Subst.compress head2 in
                                     uu____3410.FStar_Syntax_Syntax.n in
                                   match uu____3409 with
                                   | FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_reify ) -> true
                                   | uu____3413 -> false in
                                 if uu____3408
                                 then
                                   (match args with
                                    | x::[] -> Prims.fst x
                                    | uu____3429 ->
                                        failwith
                                          "Impossible : Reify applied to multiple arguments after normalization.")
                                 else e01) in
                        let e =
                          match args_e with
                          | uu____3437::[] -> e02
                          | uu____3450 ->
                              let uu____3456 =
                                let uu____3459 =
                                  let uu____3460 =
                                    let uu____3470 = FStar_List.tl args_e in
                                    (e02, uu____3470) in
                                  FStar_Syntax_Syntax.Tm_app uu____3460 in
                                FStar_Syntax_Syntax.mk uu____3459 in
                              uu____3456 None t0.FStar_Syntax_Syntax.pos in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3493),(arg,uu____3495)::[]) -> encode_term arg env
                 | uu____3513 ->
                     let uu____3521 = encode_args args_e env in
                     (match uu____3521 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3554 = encode_term head1 env in
                            match uu____3554 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3593 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3593 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3635  ->
                                                 fun uu____3636  ->
                                                   match (uu____3635,
                                                           uu____3636)
                                                   with
                                                   | ((bv,uu____3650),
                                                      (a,uu____3652)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3666 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3666
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3671 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3671 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3681 =
                                                   let uu____3685 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3690 =
                                                     let uu____3691 =
                                                       let uu____3692 =
                                                         let uu____3693 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3693 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3692 in
                                                     varops.mk_unique
                                                       uu____3691 in
                                                   (uu____3685,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3690) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3681 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3710 = lookup_free_var_sym env fv in
                            match uu____3710 with
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
                                let uu____3748 =
                                  let uu____3749 =
                                    let uu____3752 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3752 Prims.fst in
                                  FStar_All.pipe_right uu____3749 Prims.snd in
                                Some uu____3748
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3771,(FStar_Util.Inl t1,uu____3773),uu____3774)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3812,(FStar_Util.Inr c,uu____3814),uu____3815)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3853 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3873 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3873 in
                               let uu____3874 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3874 with
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
                                     | uu____3899 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3944 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3944 with
            | (bs1,body1,opening) ->
                let fallback uu____3959 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3964 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3964, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3975 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3975
                  | FStar_Util.Inr (eff,uu____3977) ->
                      let uu____3983 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3983 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body = reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4028 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___145_4029 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___145_4029.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___145_4029.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___145_4029.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___145_4029.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___145_4029.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___145_4029.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___145_4029.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___145_4029.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___145_4029.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___145_4029.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___145_4029.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___145_4029.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___145_4029.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___145_4029.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___145_4029.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___145_4029.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___145_4029.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___145_4029.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___145_4029.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___145_4029.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___145_4029.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___145_4029.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___145_4029.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4028 FStar_Syntax_Syntax.U_unknown in
                        let uu____4030 =
                          let uu____4031 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4031 in
                        FStar_Util.Inl uu____4030
                    | FStar_Util.Inr (eff_name,uu____4038) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4069 =
                        let uu____4070 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4070 in
                      FStar_All.pipe_right uu____4069
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4082 =
                        let uu____4083 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4083 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4091 =
                          let uu____4092 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4092 in
                        FStar_All.pipe_right uu____4091
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4096 =
                             let uu____4097 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4097 in
                           FStar_All.pipe_right uu____4096
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4108 =
                         let uu____4109 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4109 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4108);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4124 =
                       (is_impure lc1) &&
                         (let uu____4125 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4125) in
                     if uu____4124
                     then fallback ()
                     else
                       (let uu____4129 = encode_binders None bs1 env in
                        match uu____4129 with
                        | (vars,guards,envbody,decls,uu____4144) ->
                            let uu____4151 =
                              let uu____4159 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4159
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4151 with
                             | (lc2,body2) ->
                                 let uu____4184 = encode_term body2 envbody in
                                 (match uu____4184 with
                                  | (body3,decls') ->
                                      let key_body =
                                        let uu____4192 =
                                          let uu____4198 =
                                            let uu____4199 =
                                              let uu____4202 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____4202, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____4199 in
                                          ([], vars, uu____4198) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4192 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____4213 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____4213 with
                                       | Some (t1,uu____4228,uu____4229) ->
                                           let uu____4239 =
                                             let uu____4240 =
                                               let uu____4244 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (t1, uu____4244) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4240 in
                                           (uu____4239, [])
                                       | None  ->
                                           let uu____4255 =
                                             is_eta env vars body3 in
                                           (match uu____4255 with
                                            | Some t1 -> (t1, [])
                                            | None  ->
                                                let cvar_sorts =
                                                  FStar_List.map Prims.snd
                                                    cvars in
                                                let fsym =
                                                  let module_name =
                                                    env.current_module_name in
                                                  let fsym =
                                                    let uu____4268 =
                                                      let uu____4269 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____4269 in
                                                    varops.mk_unique
                                                      uu____4268 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      None) in
                                                let f =
                                                  let uu____4274 =
                                                    let uu____4278 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars in
                                                    (fsym, uu____4278) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4274 in
                                                let app = mk_Apply f vars in
                                                let typing_f =
                                                  let uu____4286 =
                                                    codomain_eff lc2 in
                                                  match uu____4286 with
                                                  | None  -> []
                                                  | Some c ->
                                                      let tfun =
                                                        FStar_Syntax_Util.arrow
                                                          bs1 c in
                                                      let uu____4293 =
                                                        encode_term_pred None
                                                          tfun env f in
                                                      (match uu____4293 with
                                                       | (f_has_t,decls'') ->
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym in
                                                           let uu____4300 =
                                                             let uu____4302 =
                                                               let uu____4303
                                                                 =
                                                                 let uu____4307
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkForall
                                                                    ([[f]],
                                                                    cvars,
                                                                    f_has_t) in
                                                                 (uu____4307,
                                                                   (Some
                                                                    a_name),
                                                                   a_name) in
                                                               FStar_SMTEncoding_Term.Assume
                                                                 uu____4303 in
                                                             [uu____4302] in
                                                           FStar_List.append
                                                             decls''
                                                             uu____4300) in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____4315 =
                                                    let uu____4319 =
                                                      let uu____4320 =
                                                        let uu____4326 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars),
                                                          uu____4326) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____4320 in
                                                    (uu____4319,
                                                      (Some a_name), a_name) in
                                                  FStar_SMTEncoding_Term.Assume
                                                    uu____4315 in
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
           ((uu____4344,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4345;
                          FStar_Syntax_Syntax.lbunivs = uu____4346;
                          FStar_Syntax_Syntax.lbtyp = uu____4347;
                          FStar_Syntax_Syntax.lbeff = uu____4348;
                          FStar_Syntax_Syntax.lbdef = uu____4349;_}::uu____4350),uu____4351)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4369;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4371;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4387 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4400 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4400, [decl_e])))
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
              let uu____4442 = encode_term e1 env in
              match uu____4442 with
              | (ee1,decls1) ->
                  let uu____4449 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4449 with
                   | (xs,e21) ->
                       let uu____4463 = FStar_List.hd xs in
                       (match uu____4463 with
                        | (x1,uu____4471) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4473 = encode_body e21 env' in
                            (match uu____4473 with
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
            let uu____4495 =
              let uu____4499 =
                let uu____4500 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4500 in
              gen_term_var env uu____4499 in
            match uu____4495 with
            | (scrsym,scr',env1) ->
                let uu____4514 = encode_term e env1 in
                (match uu____4514 with
                 | (scr,decls) ->
                     let uu____4521 =
                       let encode_branch b uu____4537 =
                         match uu____4537 with
                         | (else_case,decls1) ->
                             let uu____4548 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4548 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4578  ->
                                       fun uu____4579  ->
                                         match (uu____4578, uu____4579) with
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
                                                       fun uu____4616  ->
                                                         match uu____4616
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4621 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4636 =
                                                     encode_term w1 env2 in
                                                   (match uu____4636 with
                                                    | (w2,decls21) ->
                                                        let uu____4644 =
                                                          let uu____4645 =
                                                            let uu____4648 =
                                                              let uu____4649
                                                                =
                                                                let uu____4652
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4652) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4649 in
                                                            (guard,
                                                              uu____4648) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4645 in
                                                        (uu____4644, decls21)) in
                                             (match uu____4621 with
                                              | (guard1,decls21) ->
                                                  let uu____4660 =
                                                    encode_br br env2 in
                                                  (match uu____4660 with
                                                   | (br1,decls3) ->
                                                       let uu____4668 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4668,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4521 with
                      | (match_tm,decls1) ->
                          let uu____4680 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4680, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4711 -> let uu____4712 = encode_one_pat env pat in [uu____4712]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4724 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4724
       then
         let uu____4725 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4725
       else ());
      (let uu____4727 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4727 with
       | (vars,pat_term) ->
           let uu____4737 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4760  ->
                     fun v1  ->
                       match uu____4760 with
                       | (env1,vars1) ->
                           let uu____4788 = gen_term_var env1 v1 in
                           (match uu____4788 with
                            | (xx,uu____4800,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4737 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4847 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4855 =
                        let uu____4858 = encode_const c in
                        (scrutinee, uu____4858) in
                      FStar_SMTEncoding_Util.mkEq uu____4855
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4877 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4877 with
                        | (uu____4881,uu____4882::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4884 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4905  ->
                                  match uu____4905 with
                                  | (arg,uu____4911) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4921 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4921)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4940 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4955 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4970 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4992  ->
                                  match uu____4992 with
                                  | (arg,uu____5001) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5011 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5011)) in
                      FStar_All.pipe_right uu____4970 FStar_List.flatten in
                let pat_term1 uu____5027 = encode_term pat_term env1 in
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
      let uu____5034 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5049  ->
                fun uu____5050  ->
                  match (uu____5049, uu____5050) with
                  | ((tms,decls),(t,uu____5070)) ->
                      let uu____5081 = encode_term t env in
                      (match uu____5081 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5034 with | (l1,decls) -> ((FStar_List.rev l1), decls)
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
            let uu____5119 = FStar_Syntax_Util.list_elements e in
            match uu____5119 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 []) in
          let one_pat p =
            let uu____5137 =
              let uu____5147 = FStar_Syntax_Util.unmeta p in
              FStar_All.pipe_right uu____5147 FStar_Syntax_Util.head_and_args in
            match uu____5137 with
            | (head1,args) ->
                let uu____5178 =
                  let uu____5186 =
                    let uu____5187 = FStar_Syntax_Util.un_uinst head1 in
                    uu____5187.FStar_Syntax_Syntax.n in
                  (uu____5186, args) in
                (match uu____5178 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5201,uu____5202)::(e,uu____5204)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5235)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5256 -> failwith "Unexpected pattern term") in
          let lemma_pats p =
            let elts = list_elements1 p in
            let smt_pat_or t1 =
              let uu____5289 =
                let uu____5299 = FStar_Syntax_Util.unmeta t1 in
                FStar_All.pipe_right uu____5299
                  FStar_Syntax_Util.head_and_args in
              match uu____5289 with
              | (head1,args) ->
                  let uu____5328 =
                    let uu____5336 =
                      let uu____5337 = FStar_Syntax_Util.un_uinst head1 in
                      uu____5337.FStar_Syntax_Syntax.n in
                    (uu____5336, args) in
                  (match uu____5328 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5350)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5370 -> None) in
            match elts with
            | t1::[] ->
                let uu____5388 = smt_pat_or t1 in
                (match uu____5388 with
                 | Some e ->
                     let uu____5404 = list_elements1 e in
                     FStar_All.pipe_right uu____5404
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5421 = list_elements1 branch1 in
                             FStar_All.pipe_right uu____5421
                               (FStar_List.map one_pat)))
                 | uu____5435 ->
                     let uu____5439 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat) in
                     [uu____5439])
            | uu____5470 ->
                let uu____5472 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat) in
                [uu____5472] in
          let uu____5503 =
            let uu____5519 =
              let uu____5520 = FStar_Syntax_Subst.compress t in
              uu____5520.FStar_Syntax_Syntax.n in
            match uu____5519 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5550 = FStar_Syntax_Subst.open_comp binders c in
                (match uu____5550 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5585;
                            FStar_Syntax_Syntax.effect_name = uu____5586;
                            FStar_Syntax_Syntax.result_typ = uu____5587;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5589)::(post,uu____5591)::(pats,uu____5593)::[];
                            FStar_Syntax_Syntax.flags = uu____5594;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats in
                          let uu____5628 = lemma_pats pats' in
                          (binders1, pre, post, uu____5628)
                      | uu____5647 -> failwith "impos"))
            | uu____5663 -> failwith "Impos" in
          match uu____5503 with
          | (binders,pre,post,patterns) ->
              let uu____5707 = encode_binders None binders env in
              (match uu____5707 with
               | (vars,guards,env1,decls,uu____5722) ->
                   let uu____5729 =
                     let uu____5736 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5767 =
                                 let uu____5772 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5788  ->
                                           match uu____5788 with
                                           | (t1,uu____5795) ->
                                               encode_term t1
                                                 (let uu___146_5798 = env1 in
                                                  {
                                                    bindings =
                                                      (uu___146_5798.bindings);
                                                    depth =
                                                      (uu___146_5798.depth);
                                                    tcenv =
                                                      (uu___146_5798.tcenv);
                                                    warn =
                                                      (uu___146_5798.warn);
                                                    cache =
                                                      (uu___146_5798.cache);
                                                    nolabels =
                                                      (uu___146_5798.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___146_5798.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___146_5798.current_module_name)
                                                  }))) in
                                 FStar_All.pipe_right uu____5772
                                   FStar_List.unzip in
                               match uu____5767 with
                               | (pats,decls1) -> (pats, decls1))) in
                     FStar_All.pipe_right uu____5736 FStar_List.unzip in
                   (match uu____5729 with
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
                                           let uu____5862 =
                                             let uu____5863 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5863 e in
                                           uu____5862 :: p))
                               | uu____5864 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5893 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e in
                                                 uu____5893 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5901 =
                                           let uu____5902 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort) in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5902 tl1 in
                                         aux uu____5901 vars2
                                     | uu____5903 -> pats in
                                   let uu____5907 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort) in
                                   aux uu____5907 vars) in
                        let env2 =
                          let uu___147_5909 = env1 in
                          {
                            bindings = (uu___147_5909.bindings);
                            depth = (uu___147_5909.depth);
                            tcenv = (uu___147_5909.tcenv);
                            warn = (uu___147_5909.warn);
                            cache = (uu___147_5909.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___147_5909.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___147_5909.encode_non_total_function_typ);
                            current_module_name =
                              (uu___147_5909.current_module_name)
                          } in
                        let uu____5910 =
                          let uu____5913 = FStar_Syntax_Util.unmeta pre in
                          encode_formula uu____5913 env2 in
                        (match uu____5910 with
                         | (pre1,decls'') ->
                             let uu____5918 =
                               let uu____5921 = FStar_Syntax_Util.unmeta post in
                               encode_formula uu____5921 env2 in
                             (match uu____5918 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls''')) in
                                  let uu____5928 =
                                    let uu____5929 =
                                      let uu____5935 =
                                        let uu____5936 =
                                          let uu____5939 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards) in
                                          (uu____5939, post1) in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5936 in
                                      (pats1, vars, uu____5935) in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5929 in
                                  (uu____5928, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5952 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5952
        then
          let uu____5953 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5954 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5953 uu____5954
        else () in
      let enc f r l =
        let uu____5981 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5994 = encode_term (Prims.fst x) env in
                 match uu____5994 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5981 with
        | (decls,args) ->
            let uu____6011 =
              let uu___148_6012 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___148_6012.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___148_6012.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6011, decls) in
      let const_op f r uu____6031 = let uu____6034 = f r in (uu____6034, []) in
      let un_op f l =
        let uu____6050 = FStar_List.hd l in FStar_All.pipe_left f uu____6050 in
      let bin_op f uu___120_6063 =
        match uu___120_6063 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6071 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6098 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6107  ->
                 match uu____6107 with
                 | (t,uu____6115) ->
                     let uu____6116 = encode_formula t env in
                     (match uu____6116 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6098 with
        | (decls,phis) ->
            let uu____6133 =
              let uu___149_6134 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___149_6134.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___149_6134.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6133, decls) in
      let eq_op r uu___121_6150 =
        match uu___121_6150 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6210 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6210 r [e1; e2]
        | l ->
            let uu____6230 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6230 r l in
      let mk_imp1 r uu___122_6249 =
        match uu___122_6249 with
        | (lhs,uu____6253)::(rhs,uu____6255)::[] ->
            let uu____6276 = encode_formula rhs env in
            (match uu____6276 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6285) ->
                      (l1, decls1)
                  | uu____6288 ->
                      let uu____6289 = encode_formula lhs env in
                      (match uu____6289 with
                       | (l2,decls2) ->
                           let uu____6296 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6296, (FStar_List.append decls1 decls2)))))
        | uu____6298 -> failwith "impossible" in
      let mk_ite r uu___123_6313 =
        match uu___123_6313 with
        | (guard,uu____6317)::(_then,uu____6319)::(_else,uu____6321)::[] ->
            let uu____6350 = encode_formula guard env in
            (match uu____6350 with
             | (g,decls1) ->
                 let uu____6357 = encode_formula _then env in
                 (match uu____6357 with
                  | (t,decls2) ->
                      let uu____6364 = encode_formula _else env in
                      (match uu____6364 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6373 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6392 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6392 in
      let connectives =
        let uu____6404 =
          let uu____6413 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6413) in
        let uu____6426 =
          let uu____6436 =
            let uu____6445 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6445) in
          let uu____6458 =
            let uu____6468 =
              let uu____6478 =
                let uu____6487 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6487) in
              let uu____6500 =
                let uu____6510 =
                  let uu____6520 =
                    let uu____6529 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6529) in
                  [uu____6520;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6510 in
              uu____6478 :: uu____6500 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6468 in
          uu____6436 :: uu____6458 in
        uu____6404 :: uu____6426 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6691 = encode_formula phi' env in
            (match uu____6691 with
             | (phi2,decls) ->
                 let uu____6698 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6698, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6699 ->
            let uu____6704 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6704 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6733 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6733 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6741;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6743;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6759 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6759 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6791::(x,uu____6793)::(t,uu____6795)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6829 = encode_term x env in
                 (match uu____6829 with
                  | (x1,decls) ->
                      let uu____6836 = encode_term t env in
                      (match uu____6836 with
                       | (t1,decls') ->
                           let uu____6843 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6843, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6847)::(msg,uu____6849)::(phi2,uu____6851)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6885 =
                   let uu____6888 =
                     let uu____6889 = FStar_Syntax_Subst.compress r in
                     uu____6889.FStar_Syntax_Syntax.n in
                   let uu____6892 =
                     let uu____6893 = FStar_Syntax_Subst.compress msg in
                     uu____6893.FStar_Syntax_Syntax.n in
                   (uu____6888, uu____6892) in
                 (match uu____6885 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6900))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6916 -> fallback phi2)
             | uu____6919 when head_redex env head2 ->
                 let uu____6927 = whnf env phi1 in
                 encode_formula uu____6927 env
             | uu____6928 ->
                 let uu____6936 = encode_term phi1 env in
                 (match uu____6936 with
                  | (tt,decls) ->
                      let uu____6943 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___150_6944 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___150_6944.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___150_6944.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6943, decls)))
        | uu____6947 ->
            let uu____6948 = encode_term phi1 env in
            (match uu____6948 with
             | (tt,decls) ->
                 let uu____6955 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___151_6956 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___151_6956.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___151_6956.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6955, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6983 = encode_binders None bs env1 in
        match uu____6983 with
        | (vars,guards,env2,decls,uu____7005) ->
            let uu____7012 =
              let uu____7019 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7042 =
                          let uu____7047 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7061  ->
                                    match uu____7061 with
                                    | (t,uu____7067) ->
                                        encode_term t
                                          (let uu___152_7068 = env2 in
                                           {
                                             bindings =
                                               (uu___152_7068.bindings);
                                             depth = (uu___152_7068.depth);
                                             tcenv = (uu___152_7068.tcenv);
                                             warn = (uu___152_7068.warn);
                                             cache = (uu___152_7068.cache);
                                             nolabels =
                                               (uu___152_7068.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___152_7068.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___152_7068.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7047 FStar_List.unzip in
                        match uu____7042 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7019 FStar_List.unzip in
            (match uu____7012 with
             | (pats,decls') ->
                 let uu____7120 = encode_formula body env2 in
                 (match uu____7120 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7139;
                             FStar_SMTEncoding_Term.rng = uu____7140;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7148 -> guards in
                      let uu____7151 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7151, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7185  ->
                   match uu____7185 with
                   | (x,uu____7189) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7195 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7201 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7201) uu____7195 tl1 in
             let uu____7203 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7215  ->
                       match uu____7215 with
                       | (b,uu____7219) ->
                           let uu____7220 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7220)) in
             (match uu____7203 with
              | None  -> ()
              | Some (x,uu____7224) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7234 =
                    let uu____7235 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7235 in
                  FStar_Errors.warn pos uu____7234) in
       let uu____7236 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7236 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7242 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7278  ->
                     match uu____7278 with
                     | (l,uu____7288) -> FStar_Ident.lid_equals op l)) in
           (match uu____7242 with
            | None  -> fallback phi1
            | Some (uu____7311,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7340 = encode_q_body env vars pats body in
             match uu____7340 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7366 =
                     let uu____7372 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7372) in
                   FStar_SMTEncoding_Term.mkForall uu____7366
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7384 = encode_q_body env vars pats body in
             match uu____7384 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7409 =
                   let uu____7410 =
                     let uu____7416 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7416) in
                   FStar_SMTEncoding_Term.mkExists uu____7410
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7409, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7465 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7465 with
  | (asym,a) ->
      let uu____7470 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7470 with
       | (xsym,x) ->
           let uu____7475 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7475 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7505 =
                      let uu____7511 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7511, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7505 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7526 =
                      let uu____7530 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7530) in
                    FStar_SMTEncoding_Util.mkApp uu____7526 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7538 =
                    let uu____7540 =
                      let uu____7542 =
                        let uu____7544 =
                          let uu____7545 =
                            let uu____7549 =
                              let uu____7550 =
                                let uu____7556 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7556) in
                              FStar_SMTEncoding_Util.mkForall uu____7550 in
                            (uu____7549, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Term.Assume uu____7545 in
                        let uu____7565 =
                          let uu____7567 =
                            let uu____7568 =
                              let uu____7572 =
                                let uu____7573 =
                                  let uu____7579 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7579) in
                                FStar_SMTEncoding_Util.mkForall uu____7573 in
                              (uu____7572,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Term.Assume uu____7568 in
                          [uu____7567] in
                        uu____7544 :: uu____7565 in
                      xtok_decl :: uu____7542 in
                    xname_decl :: uu____7540 in
                  (xtok1, uu____7538) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7628 =
                    let uu____7636 =
                      let uu____7642 =
                        let uu____7643 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7643 in
                      quant axy uu____7642 in
                    (FStar_Syntax_Const.op_Eq, uu____7636) in
                  let uu____7649 =
                    let uu____7658 =
                      let uu____7666 =
                        let uu____7672 =
                          let uu____7673 =
                            let uu____7674 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7674 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7673 in
                        quant axy uu____7672 in
                      (FStar_Syntax_Const.op_notEq, uu____7666) in
                    let uu____7680 =
                      let uu____7689 =
                        let uu____7697 =
                          let uu____7703 =
                            let uu____7704 =
                              let uu____7705 =
                                let uu____7708 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7709 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7708, uu____7709) in
                              FStar_SMTEncoding_Util.mkLT uu____7705 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7704 in
                          quant xy uu____7703 in
                        (FStar_Syntax_Const.op_LT, uu____7697) in
                      let uu____7715 =
                        let uu____7724 =
                          let uu____7732 =
                            let uu____7738 =
                              let uu____7739 =
                                let uu____7740 =
                                  let uu____7743 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7744 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7743, uu____7744) in
                                FStar_SMTEncoding_Util.mkLTE uu____7740 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7739 in
                            quant xy uu____7738 in
                          (FStar_Syntax_Const.op_LTE, uu____7732) in
                        let uu____7750 =
                          let uu____7759 =
                            let uu____7767 =
                              let uu____7773 =
                                let uu____7774 =
                                  let uu____7775 =
                                    let uu____7778 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7779 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7778, uu____7779) in
                                  FStar_SMTEncoding_Util.mkGT uu____7775 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7774 in
                              quant xy uu____7773 in
                            (FStar_Syntax_Const.op_GT, uu____7767) in
                          let uu____7785 =
                            let uu____7794 =
                              let uu____7802 =
                                let uu____7808 =
                                  let uu____7809 =
                                    let uu____7810 =
                                      let uu____7813 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7814 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7813, uu____7814) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7810 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7809 in
                                quant xy uu____7808 in
                              (FStar_Syntax_Const.op_GTE, uu____7802) in
                            let uu____7820 =
                              let uu____7829 =
                                let uu____7837 =
                                  let uu____7843 =
                                    let uu____7844 =
                                      let uu____7845 =
                                        let uu____7848 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7849 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7848, uu____7849) in
                                      FStar_SMTEncoding_Util.mkSub uu____7845 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7844 in
                                  quant xy uu____7843 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7837) in
                              let uu____7855 =
                                let uu____7864 =
                                  let uu____7872 =
                                    let uu____7878 =
                                      let uu____7879 =
                                        let uu____7880 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7880 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7879 in
                                    quant qx uu____7878 in
                                  (FStar_Syntax_Const.op_Minus, uu____7872) in
                                let uu____7886 =
                                  let uu____7895 =
                                    let uu____7903 =
                                      let uu____7909 =
                                        let uu____7910 =
                                          let uu____7911 =
                                            let uu____7914 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7915 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7914, uu____7915) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7911 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7910 in
                                      quant xy uu____7909 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7903) in
                                  let uu____7921 =
                                    let uu____7930 =
                                      let uu____7938 =
                                        let uu____7944 =
                                          let uu____7945 =
                                            let uu____7946 =
                                              let uu____7949 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7950 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7949, uu____7950) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7946 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7945 in
                                        quant xy uu____7944 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7938) in
                                    let uu____7956 =
                                      let uu____7965 =
                                        let uu____7973 =
                                          let uu____7979 =
                                            let uu____7980 =
                                              let uu____7981 =
                                                let uu____7984 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7985 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7984, uu____7985) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7981 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7980 in
                                          quant xy uu____7979 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7973) in
                                      let uu____7991 =
                                        let uu____8000 =
                                          let uu____8008 =
                                            let uu____8014 =
                                              let uu____8015 =
                                                let uu____8016 =
                                                  let uu____8019 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8020 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8019, uu____8020) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8016 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8015 in
                                            quant xy uu____8014 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8008) in
                                        let uu____8026 =
                                          let uu____8035 =
                                            let uu____8043 =
                                              let uu____8049 =
                                                let uu____8050 =
                                                  let uu____8051 =
                                                    let uu____8054 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8055 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8054, uu____8055) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8051 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8050 in
                                              quant xy uu____8049 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8043) in
                                          let uu____8061 =
                                            let uu____8070 =
                                              let uu____8078 =
                                                let uu____8084 =
                                                  let uu____8085 =
                                                    let uu____8086 =
                                                      let uu____8089 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8090 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8089,
                                                        uu____8090) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8086 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8085 in
                                                quant xy uu____8084 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8078) in
                                            let uu____8096 =
                                              let uu____8105 =
                                                let uu____8113 =
                                                  let uu____8119 =
                                                    let uu____8120 =
                                                      let uu____8121 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8121 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8120 in
                                                  quant qx uu____8119 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8113) in
                                              [uu____8105] in
                                            uu____8070 :: uu____8096 in
                                          uu____8035 :: uu____8061 in
                                        uu____8000 :: uu____8026 in
                                      uu____7965 :: uu____7991 in
                                    uu____7930 :: uu____7956 in
                                  uu____7895 :: uu____7921 in
                                uu____7864 :: uu____7886 in
                              uu____7829 :: uu____7855 in
                            uu____7794 :: uu____7820 in
                          uu____7759 :: uu____7785 in
                        uu____7724 :: uu____7750 in
                      uu____7689 :: uu____7715 in
                    uu____7658 :: uu____7680 in
                  uu____7628 :: uu____7649 in
                let mk1 l v1 =
                  let uu____8249 =
                    let uu____8254 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8286  ->
                              match uu____8286 with
                              | (l',uu____8295) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8254
                      (FStar_Option.map
                         (fun uu____8328  ->
                            match uu____8328 with | (uu____8339,b) -> b v1)) in
                  FStar_All.pipe_right uu____8249 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8380  ->
                          match uu____8380 with
                          | (l',uu____8389) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8415 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8415 with
        | (xxsym,xx) ->
            let uu____8420 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8420 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8428 =
                   let uu____8432 =
                     let uu____8433 =
                       let uu____8439 =
                         let uu____8440 =
                           let uu____8443 =
                             let uu____8444 =
                               let uu____8447 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8447) in
                             FStar_SMTEncoding_Util.mkEq uu____8444 in
                           (xx_has_type, uu____8443) in
                         FStar_SMTEncoding_Util.mkImp uu____8440 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8439) in
                     FStar_SMTEncoding_Util.mkForall uu____8433 in
                   let uu____8460 =
                     let uu____8461 =
                       let uu____8462 =
                         let uu____8463 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8463 in
                       Prims.strcat module_name uu____8462 in
                     varops.mk_unique uu____8461 in
                   (uu____8432, (Some "pretyping"), uu____8460) in
                 FStar_SMTEncoding_Term.Assume uu____8428)
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
    let uu____8493 =
      let uu____8494 =
        let uu____8498 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8498, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Term.Assume uu____8494 in
    let uu____8500 =
      let uu____8502 =
        let uu____8503 =
          let uu____8507 =
            let uu____8508 =
              let uu____8514 =
                let uu____8515 =
                  let uu____8518 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8518) in
                FStar_SMTEncoding_Util.mkImp uu____8515 in
              ([[typing_pred]], [xx], uu____8514) in
            mkForall_fuel uu____8508 in
          (uu____8507, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8503 in
      [uu____8502] in
    uu____8493 :: uu____8500 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8546 =
      let uu____8547 =
        let uu____8551 =
          let uu____8552 =
            let uu____8558 =
              let uu____8561 =
                let uu____8563 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8563] in
              [uu____8561] in
            let uu____8566 =
              let uu____8567 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8567 tt in
            (uu____8558, [bb], uu____8566) in
          FStar_SMTEncoding_Util.mkForall uu____8552 in
        (uu____8551, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Term.Assume uu____8547 in
    let uu____8578 =
      let uu____8580 =
        let uu____8581 =
          let uu____8585 =
            let uu____8586 =
              let uu____8592 =
                let uu____8593 =
                  let uu____8596 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8596) in
                FStar_SMTEncoding_Util.mkImp uu____8593 in
              ([[typing_pred]], [xx], uu____8592) in
            mkForall_fuel uu____8586 in
          (uu____8585, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8581 in
      [uu____8580] in
    uu____8546 :: uu____8578 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8630 =
        let uu____8631 =
          let uu____8635 =
            let uu____8637 =
              let uu____8639 =
                let uu____8641 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8642 =
                  let uu____8644 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8644] in
                uu____8641 :: uu____8642 in
              tt :: uu____8639 in
            tt :: uu____8637 in
          ("Prims.Precedes", uu____8635) in
        FStar_SMTEncoding_Util.mkApp uu____8631 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8630 in
    let precedes_y_x =
      let uu____8647 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8647 in
    let uu____8649 =
      let uu____8650 =
        let uu____8654 =
          let uu____8655 =
            let uu____8661 =
              let uu____8664 =
                let uu____8666 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8666] in
              [uu____8664] in
            let uu____8669 =
              let uu____8670 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8670 tt in
            (uu____8661, [bb], uu____8669) in
          FStar_SMTEncoding_Util.mkForall uu____8655 in
        (uu____8654, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Term.Assume uu____8650 in
    let uu____8681 =
      let uu____8683 =
        let uu____8684 =
          let uu____8688 =
            let uu____8689 =
              let uu____8695 =
                let uu____8696 =
                  let uu____8699 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8699) in
                FStar_SMTEncoding_Util.mkImp uu____8696 in
              ([[typing_pred]], [xx], uu____8695) in
            mkForall_fuel uu____8689 in
          (uu____8688, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8684 in
      let uu____8712 =
        let uu____8714 =
          let uu____8715 =
            let uu____8719 =
              let uu____8720 =
                let uu____8726 =
                  let uu____8727 =
                    let uu____8730 =
                      let uu____8731 =
                        let uu____8733 =
                          let uu____8735 =
                            let uu____8737 =
                              let uu____8738 =
                                let uu____8741 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8742 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8741, uu____8742) in
                              FStar_SMTEncoding_Util.mkGT uu____8738 in
                            let uu____8743 =
                              let uu____8745 =
                                let uu____8746 =
                                  let uu____8749 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8750 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8749, uu____8750) in
                                FStar_SMTEncoding_Util.mkGTE uu____8746 in
                              let uu____8751 =
                                let uu____8753 =
                                  let uu____8754 =
                                    let uu____8757 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8758 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8757, uu____8758) in
                                  FStar_SMTEncoding_Util.mkLT uu____8754 in
                                [uu____8753] in
                              uu____8745 :: uu____8751 in
                            uu____8737 :: uu____8743 in
                          typing_pred_y :: uu____8735 in
                        typing_pred :: uu____8733 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8731 in
                    (uu____8730, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8727 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8726) in
              mkForall_fuel uu____8720 in
            (uu____8719, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Term.Assume uu____8715 in
        [uu____8714] in
      uu____8683 :: uu____8712 in
    uu____8649 :: uu____8681 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8788 =
      let uu____8789 =
        let uu____8793 =
          let uu____8794 =
            let uu____8800 =
              let uu____8803 =
                let uu____8805 = FStar_SMTEncoding_Term.boxString b in
                [uu____8805] in
              [uu____8803] in
            let uu____8808 =
              let uu____8809 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8809 tt in
            (uu____8800, [bb], uu____8808) in
          FStar_SMTEncoding_Util.mkForall uu____8794 in
        (uu____8793, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Term.Assume uu____8789 in
    let uu____8820 =
      let uu____8822 =
        let uu____8823 =
          let uu____8827 =
            let uu____8828 =
              let uu____8834 =
                let uu____8835 =
                  let uu____8838 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8838) in
                FStar_SMTEncoding_Util.mkImp uu____8835 in
              ([[typing_pred]], [xx], uu____8834) in
            mkForall_fuel uu____8828 in
          (uu____8827, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8823 in
      [uu____8822] in
    uu____8788 :: uu____8820 in
  let mk_ref1 env reft_name uu____8860 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8871 =
        let uu____8875 =
          let uu____8877 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8877] in
        (reft_name, uu____8875) in
      FStar_SMTEncoding_Util.mkApp uu____8871 in
    let refb =
      let uu____8880 =
        let uu____8884 =
          let uu____8886 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8886] in
        (reft_name, uu____8884) in
      FStar_SMTEncoding_Util.mkApp uu____8880 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8890 =
      let uu____8891 =
        let uu____8895 =
          let uu____8896 =
            let uu____8902 =
              let uu____8903 =
                let uu____8906 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8906) in
              FStar_SMTEncoding_Util.mkImp uu____8903 in
            ([[typing_pred]], [xx; aa], uu____8902) in
          mkForall_fuel uu____8896 in
        (uu____8895, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Term.Assume uu____8891 in
    let uu____8921 =
      let uu____8923 =
        let uu____8924 =
          let uu____8928 =
            let uu____8929 =
              let uu____8935 =
                let uu____8936 =
                  let uu____8939 =
                    FStar_SMTEncoding_Util.mkAnd (typing_pred, typing_pred_b) in
                  let uu____8940 =
                    let uu____8941 =
                      let uu____8944 = FStar_SMTEncoding_Util.mkFreeV aa in
                      let uu____8945 = FStar_SMTEncoding_Util.mkFreeV bb in
                      (uu____8944, uu____8945) in
                    FStar_SMTEncoding_Util.mkEq uu____8941 in
                  (uu____8939, uu____8940) in
                FStar_SMTEncoding_Util.mkImp uu____8936 in
              ([[typing_pred; typing_pred_b]], [xx; aa; bb], uu____8935) in
            mkForall_fuel' (Prims.parse_int "2") uu____8929 in
          (uu____8928, (Some "ref typing is injective"), "ref_injectivity") in
        FStar_SMTEncoding_Term.Assume uu____8924 in
      [uu____8923] in
    uu____8890 :: uu____8921 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8987 =
      let uu____8988 =
        let uu____8992 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8992, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Term.Assume uu____8988 in
    [uu____8987] in
  let mk_and_interp env conj uu____9003 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9013 =
        let uu____9017 =
          let uu____9019 = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
          [uu____9019] in
        ("Valid", uu____9017) in
      FStar_SMTEncoding_Util.mkApp uu____9013 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9026 =
      let uu____9027 =
        let uu____9031 =
          let uu____9032 =
            let uu____9038 =
              let uu____9039 =
                let uu____9042 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9042, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9039 in
            ([[valid]], [aa; bb], uu____9038) in
          FStar_SMTEncoding_Util.mkForall uu____9032 in
        (uu____9031, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Term.Assume uu____9027 in
    [uu____9026] in
  let mk_or_interp env disj uu____9066 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9076 =
        let uu____9080 =
          let uu____9082 = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
          [uu____9082] in
        ("Valid", uu____9080) in
      FStar_SMTEncoding_Util.mkApp uu____9076 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9089 =
      let uu____9090 =
        let uu____9094 =
          let uu____9095 =
            let uu____9101 =
              let uu____9102 =
                let uu____9105 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9105, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9102 in
            ([[valid]], [aa; bb], uu____9101) in
          FStar_SMTEncoding_Util.mkForall uu____9095 in
        (uu____9094, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Term.Assume uu____9090 in
    [uu____9089] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let valid =
      let uu____9143 =
        let uu____9147 =
          let uu____9149 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
          [uu____9149] in
        ("Valid", uu____9147) in
      FStar_SMTEncoding_Util.mkApp uu____9143 in
    let uu____9152 =
      let uu____9153 =
        let uu____9157 =
          let uu____9158 =
            let uu____9164 =
              let uu____9165 =
                let uu____9168 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9168, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9165 in
            ([[valid]], [aa; xx1; yy1], uu____9164) in
          FStar_SMTEncoding_Util.mkForall uu____9158 in
        (uu____9157, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Term.Assume uu____9153 in
    [uu____9152] in
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
      let uu____9212 =
        let uu____9216 =
          let uu____9218 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
          [uu____9218] in
        ("Valid", uu____9216) in
      FStar_SMTEncoding_Util.mkApp uu____9212 in
    let uu____9221 =
      let uu____9222 =
        let uu____9226 =
          let uu____9227 =
            let uu____9233 =
              let uu____9234 =
                let uu____9237 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9237, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9234 in
            ([[valid]], [aa; bb; xx1; yy1], uu____9233) in
          FStar_SMTEncoding_Util.mkForall uu____9227 in
        (uu____9226, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Term.Assume uu____9222 in
    [uu____9221] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9275 =
        let uu____9279 =
          let uu____9281 = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
          [uu____9281] in
        ("Valid", uu____9279) in
      FStar_SMTEncoding_Util.mkApp uu____9275 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9288 =
      let uu____9289 =
        let uu____9293 =
          let uu____9294 =
            let uu____9300 =
              let uu____9301 =
                let uu____9304 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9304, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9301 in
            ([[valid]], [aa; bb], uu____9300) in
          FStar_SMTEncoding_Util.mkForall uu____9294 in
        (uu____9293, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Term.Assume uu____9289 in
    [uu____9288] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9338 =
        let uu____9342 =
          let uu____9344 = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
          [uu____9344] in
        ("Valid", uu____9342) in
      FStar_SMTEncoding_Util.mkApp uu____9338 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9351 =
      let uu____9352 =
        let uu____9356 =
          let uu____9357 =
            let uu____9363 =
              let uu____9364 =
                let uu____9367 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9367, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9364 in
            ([[valid]], [aa; bb], uu____9363) in
          FStar_SMTEncoding_Util.mkForall uu____9357 in
        (uu____9356, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Term.Assume uu____9352 in
    [uu____9351] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let valid =
      let uu____9397 =
        let uu____9401 =
          let uu____9403 = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
          [uu____9403] in
        ("Valid", uu____9401) in
      FStar_SMTEncoding_Util.mkApp uu____9397 in
    let not_valid_a =
      let uu____9407 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9407 in
    let uu____9409 =
      let uu____9410 =
        let uu____9414 =
          let uu____9415 =
            let uu____9421 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[valid]], [aa], uu____9421) in
          FStar_SMTEncoding_Util.mkForall uu____9415 in
        (uu____9414, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Term.Assume uu____9410 in
    [uu____9409] in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let valid =
      let uu____9457 =
        let uu____9461 =
          let uu____9463 = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b]) in
          [uu____9463] in
        ("Valid", uu____9461) in
      FStar_SMTEncoding_Util.mkApp uu____9457 in
    let valid_b_x =
      let uu____9467 =
        let uu____9471 =
          let uu____9473 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9473] in
        ("Valid", uu____9471) in
      FStar_SMTEncoding_Util.mkApp uu____9467 in
    let uu____9475 =
      let uu____9476 =
        let uu____9480 =
          let uu____9481 =
            let uu____9487 =
              let uu____9488 =
                let uu____9491 =
                  let uu____9492 =
                    let uu____9498 =
                      let uu____9501 =
                        let uu____9503 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9503] in
                      [uu____9501] in
                    let uu____9506 =
                      let uu____9507 =
                        let uu____9510 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9510, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9507 in
                    (uu____9498, [xx1], uu____9506) in
                  FStar_SMTEncoding_Util.mkForall uu____9492 in
                (uu____9491, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9488 in
            ([[valid]], [aa; bb], uu____9487) in
          FStar_SMTEncoding_Util.mkForall uu____9481 in
        (uu____9480, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Term.Assume uu____9476 in
    [uu____9475] in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let valid =
      let uu____9557 =
        let uu____9561 =
          let uu____9563 = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b]) in
          [uu____9563] in
        ("Valid", uu____9561) in
      FStar_SMTEncoding_Util.mkApp uu____9557 in
    let valid_b_x =
      let uu____9567 =
        let uu____9571 =
          let uu____9573 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9573] in
        ("Valid", uu____9571) in
      FStar_SMTEncoding_Util.mkApp uu____9567 in
    let uu____9575 =
      let uu____9576 =
        let uu____9580 =
          let uu____9581 =
            let uu____9587 =
              let uu____9588 =
                let uu____9591 =
                  let uu____9592 =
                    let uu____9598 =
                      let uu____9601 =
                        let uu____9603 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9603] in
                      [uu____9601] in
                    let uu____9606 =
                      let uu____9607 =
                        let uu____9610 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9610, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9607 in
                    (uu____9598, [xx1], uu____9606) in
                  FStar_SMTEncoding_Util.mkExists uu____9592 in
                (uu____9591, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9588 in
            ([[valid]], [aa; bb], uu____9587) in
          FStar_SMTEncoding_Util.mkForall uu____9581 in
        (uu____9580, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Term.Assume uu____9576 in
    [uu____9575] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9646 =
      let uu____9647 =
        let uu____9651 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9652 = varops.mk_unique "typing_range_const" in
        (uu____9651, (Some "Range_const typing"), uu____9652) in
      FStar_SMTEncoding_Term.Assume uu____9647 in
    [uu____9646] in
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
          let uu____9914 =
            FStar_Util.find_opt
              (fun uu____9932  ->
                 match uu____9932 with
                 | (l,uu____9942) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9914 with
          | None  -> []
          | Some (uu____9964,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10001 = encode_function_type_as_formula None None t env in
        match uu____10001 with
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
            let uu____10033 =
              (let uu____10034 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10034) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10033
            then
              let uu____10038 = new_term_constant_and_tok_from_lid env lid in
              match uu____10038 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10050 =
                      let uu____10051 = FStar_Syntax_Subst.compress t_norm in
                      uu____10051.FStar_Syntax_Syntax.n in
                    match uu____10050 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10056) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10073  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10076 -> [] in
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
              (let uu____10085 = prims.is lid in
               if uu____10085
               then
                 let vname = varops.new_fvar lid in
                 let uu____10090 = prims.mk lid vname in
                 match uu____10090 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10105 =
                    let uu____10111 = curried_arrow_formals_comp t_norm in
                    match uu____10111 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10122 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10122
                          then
                            let uu____10123 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___153_10124 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___153_10124.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___153_10124.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___153_10124.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___153_10124.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___153_10124.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___153_10124.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___153_10124.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___153_10124.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___153_10124.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___153_10124.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___153_10124.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___153_10124.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___153_10124.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___153_10124.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___153_10124.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___153_10124.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___153_10124.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___153_10124.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___153_10124.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___153_10124.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___153_10124.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___153_10124.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___153_10124.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10123
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10131 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10131)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10105 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10158 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10158 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10171 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___124_10195  ->
                                     match uu___124_10195 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10198 =
                                           FStar_Util.prefix vars in
                                         (match uu____10198 with
                                          | (uu____10209,(xxsym,uu____10211))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10221 =
                                                let uu____10222 =
                                                  let uu____10226 =
                                                    let uu____10227 =
                                                      let uu____10233 =
                                                        let uu____10234 =
                                                          let uu____10237 =
                                                            let uu____10238 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10238 in
                                                          (vapp, uu____10237) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10234 in
                                                      ([[vapp]], vars,
                                                        uu____10233) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10227 in
                                                  (uu____10226,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10222 in
                                              [uu____10221])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10249 =
                                           FStar_Util.prefix vars in
                                         (match uu____10249 with
                                          | (uu____10260,(xxsym,uu____10262))
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
                                              let uu____10276 =
                                                let uu____10277 =
                                                  let uu____10281 =
                                                    let uu____10282 =
                                                      let uu____10288 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10288) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10282 in
                                                  (uu____10281,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10277 in
                                              [uu____10276])
                                     | uu____10297 -> [])) in
                           let uu____10298 = encode_binders None formals env1 in
                           (match uu____10298 with
                            | (vars,guards,env',decls1,uu____10314) ->
                                let uu____10321 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10326 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10326, decls1)
                                  | Some p ->
                                      let uu____10328 = encode_formula p env' in
                                      (match uu____10328 with
                                       | (g,ds) ->
                                           let uu____10335 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10335,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10321 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10344 =
                                         let uu____10348 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10348) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10344 in
                                     let uu____10353 =
                                       let vname_decl =
                                         let uu____10358 =
                                           let uu____10364 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10369  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10364,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10358 in
                                       let uu____10374 =
                                         let env2 =
                                           let uu___154_10378 = env1 in
                                           {
                                             bindings =
                                               (uu___154_10378.bindings);
                                             depth = (uu___154_10378.depth);
                                             tcenv = (uu___154_10378.tcenv);
                                             warn = (uu___154_10378.warn);
                                             cache = (uu___154_10378.cache);
                                             nolabels =
                                               (uu___154_10378.nolabels);
                                             use_zfuel_name =
                                               (uu___154_10378.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___154_10378.current_module_name)
                                           } in
                                         let uu____10379 =
                                           let uu____10380 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10380 in
                                         if uu____10379
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10374 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10390::uu____10391 ->
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
                                                   let uu____10414 =
                                                     let uu____10420 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10420) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10414 in
                                                 FStar_SMTEncoding_Term.Assume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10434 ->
                                                 FStar_SMTEncoding_Term.Assume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10436 =
                                             match formals with
                                             | [] ->
                                                 let uu____10445 =
                                                   let uu____10446 =
                                                     let uu____10448 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10448 in
                                                   push_free_var env1 lid
                                                     vname uu____10446 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10445)
                                             | uu____10451 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10456 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10456 in
                                                 let name_tok_corr =
                                                   let uu____10458 =
                                                     let uu____10462 =
                                                       let uu____10463 =
                                                         let uu____10469 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10469) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10463 in
                                                     (uu____10462,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Term.Assume
                                                     uu____10458 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10436 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10353 with
                                      | (decls2,env2) ->
                                          let uu____10493 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10498 =
                                              encode_term res_t1 env' in
                                            match uu____10498 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10506 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10506,
                                                  decls) in
                                          (match uu____10493 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10514 =
                                                   let uu____10518 =
                                                     let uu____10519 =
                                                       let uu____10525 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10525) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10519 in
                                                   (uu____10518,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____10514 in
                                               let freshness =
                                                 let uu____10534 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10534
                                                 then
                                                   let uu____10537 =
                                                     let uu____10538 =
                                                       let uu____10544 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10550 =
                                                         varops.next_id () in
                                                       (vname, uu____10544,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10550) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10538 in
                                                   let uu____10552 =
                                                     let uu____10554 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10554] in
                                                   uu____10537 :: uu____10552
                                                 else [] in
                                               let g =
                                                 let uu____10558 =
                                                   let uu____10560 =
                                                     let uu____10562 =
                                                       let uu____10564 =
                                                         let uu____10566 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10566 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10564 in
                                                     FStar_List.append decls3
                                                       uu____10562 in
                                                   FStar_List.append decls2
                                                     uu____10560 in
                                                 FStar_List.append decls11
                                                   uu____10558 in
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
          let uu____10588 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10588 with
          | None  ->
              let uu____10611 = encode_free_var env x t t_norm [] in
              (match uu____10611 with
               | (decls,env1) ->
                   let uu____10626 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10626 with
                    | (n1,x',uu____10645) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10657) -> ((n1, x1), [], env)
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
          let uu____10690 = encode_free_var env lid t tt quals in
          match uu____10690 with
          | (decls,env1) ->
              let uu____10701 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10701
              then
                let uu____10705 =
                  let uu____10707 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10707 in
                (uu____10705, env1)
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
             (fun uu____10735  ->
                fun lb  ->
                  match uu____10735 with
                  | (decls,env1) ->
                      let uu____10747 =
                        let uu____10751 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10751
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10747 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10765 = FStar_Syntax_Util.head_and_args t in
    match uu____10765 with
    | (hd1,args) ->
        let uu____10791 =
          let uu____10792 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10792.FStar_Syntax_Syntax.n in
        (match uu____10791 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10796,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10809 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10824  ->
      fun quals  ->
        match uu____10824 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10873 = FStar_Util.first_N nbinders formals in
              match uu____10873 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10913  ->
                         fun uu____10914  ->
                           match (uu____10913, uu____10914) with
                           | ((formal,uu____10924),(binder,uu____10926)) ->
                               let uu____10931 =
                                 let uu____10936 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10936) in
                               FStar_Syntax_Syntax.NT uu____10931) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10941 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10955  ->
                              match uu____10955 with
                              | (x,i) ->
                                  let uu____10962 =
                                    let uu___155_10963 = x in
                                    let uu____10964 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___155_10963.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___155_10963.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10964
                                    } in
                                  (uu____10962, i))) in
                    FStar_All.pipe_right uu____10941
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10976 =
                      let uu____10978 =
                        let uu____10979 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10979.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10978 in
                    let uu____10983 =
                      let uu____10984 = FStar_Syntax_Subst.compress body in
                      let uu____10985 =
                        let uu____10986 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10986 in
                      FStar_Syntax_Syntax.extend_app_n uu____10984
                        uu____10985 in
                    uu____10983 uu____10976 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11028 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11028
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___156_11029 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___156_11029.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___156_11029.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___156_11029.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___156_11029.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___156_11029.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___156_11029.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___156_11029.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___156_11029.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___156_11029.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___156_11029.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___156_11029.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___156_11029.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___156_11029.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___156_11029.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___156_11029.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___156_11029.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___156_11029.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___156_11029.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___156_11029.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___156_11029.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___156_11029.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___156_11029.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___156_11029.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11050 = FStar_Syntax_Util.abs_formals e in
                match uu____11050 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11099::uu____11100 ->
                         let uu____11108 =
                           let uu____11109 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11109.FStar_Syntax_Syntax.n in
                         (match uu____11108 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11136 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11136 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11162 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11162
                                   then
                                     let uu____11180 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11180 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11226  ->
                                                   fun uu____11227  ->
                                                     match (uu____11226,
                                                             uu____11227)
                                                     with
                                                     | ((x,uu____11237),
                                                        (b,uu____11239)) ->
                                                         let uu____11244 =
                                                           let uu____11249 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11249) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11244)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11251 =
                                            let uu____11262 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11262) in
                                          (uu____11251, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11297 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11297 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11349) ->
                              let uu____11354 =
                                let uu____11365 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11365 in
                              (uu____11354, true)
                          | uu____11398 when Prims.op_Negation norm1 ->
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
                          | uu____11400 ->
                              let uu____11401 =
                                let uu____11402 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11403 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11402
                                  uu____11403 in
                              failwith uu____11401)
                     | uu____11416 ->
                         let uu____11417 =
                           let uu____11418 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11418.FStar_Syntax_Syntax.n in
                         (match uu____11417 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11445 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11445 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11463 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11463 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11511 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11539 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11539
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11546 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11587  ->
                            fun lb  ->
                              match uu____11587 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11638 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11638
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11641 =
                                      let uu____11649 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11649
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11641 with
                                    | (tok,decl,env2) ->
                                        let uu____11674 =
                                          let uu____11681 =
                                            let uu____11687 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11687, tok) in
                                          uu____11681 :: toks in
                                        (uu____11674, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11546 with
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
                        | uu____11789 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11794 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11794 vars)
                            else
                              (let uu____11796 =
                                 let uu____11800 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11800) in
                               FStar_SMTEncoding_Util.mkApp uu____11796) in
                      let uu____11805 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___125_11807  ->
                                 match uu___125_11807 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11808 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11811 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11811))) in
                      if uu____11805
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11831;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11833;
                                FStar_Syntax_Syntax.lbeff = uu____11834;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11875 =
                                 FStar_Syntax_Subst.univ_var_opening uvs in
                               (match uu____11875 with
                                | (univ_subst,univ_vars1) ->
                                    let env' =
                                      let uu___159_11890 = env1 in
                                      let uu____11891 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1.tcenv univ_vars1 in
                                      {
                                        bindings = (uu___159_11890.bindings);
                                        depth = (uu___159_11890.depth);
                                        tcenv = uu____11891;
                                        warn = (uu___159_11890.warn);
                                        cache = (uu___159_11890.cache);
                                        nolabels = (uu___159_11890.nolabels);
                                        use_zfuel_name =
                                          (uu___159_11890.use_zfuel_name);
                                        encode_non_total_function_typ =
                                          (uu___159_11890.encode_non_total_function_typ);
                                        current_module_name =
                                          (uu___159_11890.current_module_name)
                                      } in
                                    let t_norm1 =
                                      FStar_Syntax_Subst.subst univ_subst
                                        t_norm in
                                    let e1 =
                                      let uu____11894 =
                                        FStar_Syntax_Subst.subst univ_subst e in
                                      FStar_Syntax_Subst.compress uu____11894 in
                                    let uu____11895 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11895 with
                                     | ((binders,body,uu____11907,uu____11908),curry)
                                         ->
                                         ((let uu____11915 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11915
                                           then
                                             let uu____11916 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11917 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11916 uu____11917
                                           else ());
                                          (let uu____11919 =
                                             encode_binders None binders env' in
                                           match uu____11919 with
                                           | (vars,guards,env'1,binder_decls,uu____11935)
                                               ->
                                               let body1 =
                                                 let uu____11943 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11943
                                                 then
                                                   reify_body env'1.tcenv
                                                     body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11946 =
                                                 let uu____11951 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11951
                                                 then
                                                   let uu____11957 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11958 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11957, uu____11958)
                                                 else
                                                   (let uu____11964 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11964)) in
                                               (match uu____11946 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11978 =
                                                        let uu____11982 =
                                                          let uu____11983 =
                                                            let uu____11989 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11989) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11983 in
                                                        let uu____11995 =
                                                          let uu____11997 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11997 in
                                                        (uu____11982,
                                                          uu____11995,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Term.Assume
                                                        uu____11978 in
                                                    let uu____11999 =
                                                      let uu____12001 =
                                                        let uu____12003 =
                                                          let uu____12005 =
                                                            let uu____12007 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12007 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12005 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12003 in
                                                      FStar_List.append
                                                        decls1 uu____12001 in
                                                    (uu____11999, env1))))))
                           | uu____12010 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12029 = varops.fresh "fuel" in
                             (uu____12029, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12032 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12071  ->
                                     fun uu____12072  ->
                                       match (uu____12071, uu____12072) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12154 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12154 in
                                           let gtok =
                                             let uu____12156 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12156 in
                                           let env3 =
                                             let uu____12158 =
                                               let uu____12160 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12160 in
                                             push_free_var env2 flid gtok
                                               uu____12158 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12032 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12244
                                 t_norm uu____12246 =
                                 match (uu____12244, uu____12246) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12271;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12272;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12289 =
                                       FStar_Syntax_Subst.univ_var_opening
                                         uvs in
                                     (match uu____12289 with
                                      | (univ_subst,univ_vars1) ->
                                          let env' =
                                            let uu___160_12306 = env2 in
                                            let uu____12307 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env2.tcenv univ_vars1 in
                                            {
                                              bindings =
                                                (uu___160_12306.bindings);
                                              depth = (uu___160_12306.depth);
                                              tcenv = uu____12307;
                                              warn = (uu___160_12306.warn);
                                              cache = (uu___160_12306.cache);
                                              nolabels =
                                                (uu___160_12306.nolabels);
                                              use_zfuel_name =
                                                (uu___160_12306.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___160_12306.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___160_12306.current_module_name)
                                            } in
                                          let t_norm1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst t_norm in
                                          let e1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst e in
                                          ((let uu____12311 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12311
                                            then
                                              let uu____12312 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12313 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12314 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12312 uu____12313
                                                uu____12314
                                            else ());
                                           (let uu____12316 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12316 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12338 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12338
                                                  then
                                                    let uu____12339 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12340 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12341 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12342 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12339 uu____12340
                                                      uu____12341 uu____12342
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12346 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12346 with
                                                  | (vars,guards,env'1,binder_decls,uu____12364)
                                                      ->
                                                      let decl_g =
                                                        let uu____12372 =
                                                          let uu____12378 =
                                                            let uu____12380 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12380 in
                                                          (g, uu____12378,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12372 in
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
                                                        let uu____12395 =
                                                          let uu____12399 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12399) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12395 in
                                                      let gsapp =
                                                        let uu____12405 =
                                                          let uu____12409 =
                                                            let uu____12411 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12411 ::
                                                              vars_tm in
                                                          (g, uu____12409) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12405 in
                                                      let gmax =
                                                        let uu____12415 =
                                                          let uu____12419 =
                                                            let uu____12421 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12421 ::
                                                              vars_tm in
                                                          (g, uu____12419) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12415 in
                                                      let body1 =
                                                        let uu____12425 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12425
                                                        then
                                                          reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12427 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12427 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12438
                                                               =
                                                               let uu____12442
                                                                 =
                                                                 let uu____12443
                                                                   =
                                                                   let uu____12451
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
                                                                    uu____12451) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12443 in
                                                               let uu____12462
                                                                 =
                                                                 let uu____12464
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12464 in
                                                               (uu____12442,
                                                                 uu____12462,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12438 in
                                                           let eqn_f =
                                                             let uu____12467
                                                               =
                                                               let uu____12471
                                                                 =
                                                                 let uu____12472
                                                                   =
                                                                   let uu____12478
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12478) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12472 in
                                                               (uu____12471,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12467 in
                                                           let eqn_g' =
                                                             let uu____12486
                                                               =
                                                               let uu____12490
                                                                 =
                                                                 let uu____12491
                                                                   =
                                                                   let uu____12497
                                                                    =
                                                                    let uu____12498
                                                                    =
                                                                    let uu____12501
                                                                    =
                                                                    let uu____12502
                                                                    =
                                                                    let uu____12506
                                                                    =
                                                                    let uu____12508
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12508
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12506) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12502 in
                                                                    (gsapp,
                                                                    uu____12501) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12498 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12497) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12491 in
                                                               (uu____12490,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12486 in
                                                           let uu____12520 =
                                                             let uu____12525
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12525
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12542)
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
                                                                    let uu____12557
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12557
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12560
                                                                    =
                                                                    let uu____12564
                                                                    =
                                                                    let uu____12565
                                                                    =
                                                                    let uu____12571
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12571) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12565 in
                                                                    (uu____12564,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Term.Assume
                                                                    uu____12560 in
                                                                 let uu____12582
                                                                   =
                                                                   let uu____12586
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12586
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12594
                                                                    =
                                                                    let uu____12596
                                                                    =
                                                                    let uu____12597
                                                                    =
                                                                    let uu____12601
                                                                    =
                                                                    let uu____12602
                                                                    =
                                                                    let uu____12608
                                                                    =
                                                                    let uu____12609
                                                                    =
                                                                    let uu____12612
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12612,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12609 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12608) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12602 in
                                                                    (uu____12601,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12597 in
                                                                    [uu____12596] in
                                                                    (d3,
                                                                    uu____12594) in
                                                                 (match uu____12582
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12520
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
                               let uu____12647 =
                                 let uu____12654 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12686  ->
                                      fun uu____12687  ->
                                        match (uu____12686, uu____12687) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12763 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12763 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12654 in
                               (match uu____12647 with
                                | (decls2,eqns,env01) ->
                                    let uu____12803 =
                                      let isDeclFun uu___126_12811 =
                                        match uu___126_12811 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12812 -> true
                                        | uu____12818 -> false in
                                      let uu____12819 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12819
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12803 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12846 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12846
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
      (let uu____12879 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____12879
       then
         let uu____12880 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
           uu____12880
       else ());
      (let nm =
         let uu____12883 = FStar_Syntax_Util.lid_of_sigelt se in
         match uu____12883 with | None  -> "" | Some l -> l.FStar_Ident.str in
       let uu____12886 = encode_sigelt' env se in
       match uu____12886 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12895 =
                  let uu____12897 =
                    let uu____12898 = FStar_Util.format1 "<Skipped %s/>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12898 in
                  [uu____12897] in
                (uu____12895, e)
            | uu____12900 ->
                let uu____12901 =
                  let uu____12903 =
                    let uu____12905 =
                      let uu____12906 =
                        FStar_Util.format1 "<Start encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12906 in
                    uu____12905 :: g in
                  let uu____12907 =
                    let uu____12909 =
                      let uu____12910 =
                        FStar_Util.format1 "</end encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12910 in
                    [uu____12909] in
                  FStar_List.append uu____12903 uu____12907 in
                (uu____12901, e)))
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12918 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12927 =
            let uu____12928 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12928 Prims.op_Negation in
          if uu____12927
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12948 ->
                   let uu____12949 =
                     let uu____12952 =
                       let uu____12953 =
                         let uu____12968 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12968) in
                       FStar_Syntax_Syntax.Tm_abs uu____12953 in
                     FStar_Syntax_Syntax.mk uu____12952 in
                   uu____12949 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13021 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13021 with
               | (aname,atok,env2) ->
                   let uu____13031 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13031 with
                    | (formals,uu____13041) ->
                        let uu____13048 =
                          let uu____13051 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13051 env2 in
                        (match uu____13048 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13059 =
                                 let uu____13060 =
                                   let uu____13066 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13074  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13066,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13060 in
                               [uu____13059;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13081 =
                               let aux uu____13110 uu____13111 =
                                 match (uu____13110, uu____13111) with
                                 | ((bv,uu____13138),(env3,acc_sorts,acc)) ->
                                     let uu____13159 = gen_term_var env3 bv in
                                     (match uu____13159 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13081 with
                              | (uu____13197,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13211 =
                                      let uu____13215 =
                                        let uu____13216 =
                                          let uu____13222 =
                                            let uu____13223 =
                                              let uu____13226 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13226) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13223 in
                                          ([[app]], xs_sorts, uu____13222) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13216 in
                                      (uu____13215, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Term.Assume uu____13211 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13238 =
                                      let uu____13242 =
                                        let uu____13243 =
                                          let uu____13249 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13249) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13243 in
                                      (uu____13242,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Term.Assume uu____13238 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13259 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13259 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____13275,uu____13276,uu____13277) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13280 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13280 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13291,t,quals) ->
          let will_encode_definition =
            let uu____13297 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___127_13299  ->
                      match uu___127_13299 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13302 -> false)) in
            Prims.op_Negation uu____13297 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13308 = encode_top_level_val env fv t quals in
             match uu____13308 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13320 =
                   let uu____13322 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13322 in
                 (uu____13320, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____13327) ->
          let uu____13330 = encode_formula f env in
          (match uu____13330 with
           | (f1,decls) ->
               let g =
                 let uu____13339 =
                   let uu____13340 =
                     let uu____13344 =
                       let uu____13346 =
                         let uu____13347 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13347 in
                       Some uu____13346 in
                     let uu____13348 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13344, uu____13348) in
                   FStar_SMTEncoding_Term.Assume uu____13340 in
                 [uu____13339] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13352,quals,uu____13354) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13362 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13369 =
                       let uu____13374 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13374.FStar_Syntax_Syntax.fv_name in
                     uu____13369.FStar_Syntax_Syntax.v in
                   let uu____13378 =
                     let uu____13379 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13379 in
                   if uu____13378
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
                     let uu____13398 = encode_sigelt' env1 val_decl in
                     match uu____13398 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13362 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13415,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13417;
                          FStar_Syntax_Syntax.lbtyp = uu____13418;
                          FStar_Syntax_Syntax.lbeff = uu____13419;
                          FStar_Syntax_Syntax.lbdef = uu____13420;_}::[]),uu____13421,uu____13422,uu____13423)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13439 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13439 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let valid_b2t_x =
                 let uu____13457 =
                   let uu____13461 =
                     let uu____13463 =
                       FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
                     [uu____13463] in
                   ("Valid", uu____13461) in
                 FStar_SMTEncoding_Util.mkApp uu____13457 in
               let decls =
                 let uu____13468 =
                   let uu____13470 =
                     let uu____13471 =
                       let uu____13475 =
                         let uu____13476 =
                           let uu____13482 =
                             let uu____13483 =
                               let uu____13486 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13486) in
                             FStar_SMTEncoding_Util.mkEq uu____13483 in
                           ([[valid_b2t_x]], [xx], uu____13482) in
                         FStar_SMTEncoding_Util.mkForall uu____13476 in
                       (uu____13475, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Term.Assume uu____13471 in
                   [uu____13470] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13468 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let
          (uu____13503,uu____13504,quals,uu____13506) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___128_13514  ->
                  match uu___128_13514 with
                  | FStar_Syntax_Syntax.Discriminator uu____13515 -> true
                  | uu____13516 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13518,lids,quals,uu____13521) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13530 =
                     let uu____13531 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13531.FStar_Ident.idText in
                   uu____13530 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___129_13533  ->
                     match uu___129_13533 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13534 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13537,quals,uu____13539) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___130_13551  ->
                  match uu___130_13551 with
                  | FStar_Syntax_Syntax.Projector uu____13552 -> true
                  | uu____13555 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13562 = try_lookup_free_var env l in
          (match uu____13562 with
           | Some uu____13566 -> ([], env)
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
          ((is_rec,bindings),uu____13575,quals,uu____13577) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13591,uu____13592) ->
          let uu____13599 = encode_signature env ses in
          (match uu____13599 with
           | (g,env1) ->
               let uu____13609 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___131_13619  ->
                         match uu___131_13619 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13620,Some "inversion axiom",uu____13621)
                             -> false
                         | uu____13623 -> true)) in
               (match uu____13609 with
                | (g',inversions) ->
                    let uu____13632 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___132_13642  ->
                              match uu___132_13642 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13643 ->
                                  true
                              | uu____13649 -> false)) in
                    (match uu____13632 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13660,tps,k,uu____13663,datas,quals) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___133_13674  ->
                    match uu___133_13674 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13675 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13682 = c in
              match uu____13682 with
              | (name,args,uu____13686,uu____13687,uu____13688) ->
                  let uu____13691 =
                    let uu____13692 =
                      let uu____13698 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13705  ->
                                match uu____13705 with
                                | (uu____13709,sort,uu____13711) -> sort)) in
                      (name, uu____13698, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13692 in
                  [uu____13691]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13729 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13732 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13732 FStar_Option.isNone)) in
            if uu____13729
            then []
            else
              (let uu____13749 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13749 with
               | (xxsym,xx) ->
                   let uu____13755 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13766  ->
                             fun l  ->
                               match uu____13766 with
                               | (out,decls) ->
                                   let uu____13778 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13778 with
                                    | (uu____13784,data_t) ->
                                        let uu____13786 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13786 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13815 =
                                                 let uu____13816 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13816.FStar_Syntax_Syntax.n in
                                               match uu____13815 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13824,indices) ->
                                                   indices
                                               | uu____13840 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13852  ->
                                                         match uu____13852
                                                         with
                                                         | (x,uu____13856) ->
                                                             let uu____13857
                                                               =
                                                               let uu____13858
                                                                 =
                                                                 let uu____13862
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13862,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13858 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13857)
                                                    env) in
                                             let uu____13864 =
                                               encode_args indices env1 in
                                             (match uu____13864 with
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
                                                      let uu____13884 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13892
                                                                 =
                                                                 let uu____13895
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13895,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13892)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13884
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13897 =
                                                      let uu____13898 =
                                                        let uu____13901 =
                                                          let uu____13902 =
                                                            let uu____13905 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13905,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13902 in
                                                        (out, uu____13901) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13898 in
                                                    (uu____13897,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13755 with
                    | (data_ax,decls) ->
                        let uu____13913 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13913 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13924 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13924 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13927 =
                                 let uu____13931 =
                                   let uu____13932 =
                                     let uu____13938 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13946 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13938,
                                       uu____13946) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13932 in
                                 let uu____13954 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13931, (Some "inversion axiom"),
                                   uu____13954) in
                               FStar_SMTEncoding_Term.Assume uu____13927 in
                             let pattern_guarded_inversion =
                               let uu____13958 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13958
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13966 =
                                   let uu____13967 =
                                     let uu____13971 =
                                       let uu____13972 =
                                         let uu____13978 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13986 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13978, uu____13986) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13972 in
                                     let uu____13994 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13971, (Some "inversion axiom"),
                                       uu____13994) in
                                   FStar_SMTEncoding_Term.Assume uu____13967 in
                                 [uu____13966]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13997 =
            let uu____14005 =
              let uu____14006 = FStar_Syntax_Subst.compress k in
              uu____14006.FStar_Syntax_Syntax.n in
            match uu____14005 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14035 -> (tps, k) in
          (match uu____13997 with
           | (formals,res) ->
               let uu____14050 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14050 with
                | (formals1,res1) ->
                    let uu____14057 = encode_binders None formals1 env in
                    (match uu____14057 with
                     | (vars,guards,env',binder_decls,uu____14072) ->
                         let uu____14079 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14079 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14092 =
                                  let uu____14096 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14096) in
                                FStar_SMTEncoding_Util.mkApp uu____14092 in
                              let uu____14101 =
                                let tname_decl =
                                  let uu____14107 =
                                    let uu____14108 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14123  ->
                                              match uu____14123 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14131 = varops.next_id () in
                                    (tname, uu____14108,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14131, false) in
                                  constructor_or_logic_type_decl uu____14107 in
                                let uu____14136 =
                                  match vars with
                                  | [] ->
                                      let uu____14143 =
                                        let uu____14144 =
                                          let uu____14146 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14146 in
                                        push_free_var env1 t tname
                                          uu____14144 in
                                      ([], uu____14143)
                                  | uu____14150 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14156 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14156 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14165 =
                                          let uu____14169 =
                                            let uu____14170 =
                                              let uu____14178 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14178) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14170 in
                                          (uu____14169,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____14165 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14136 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14101 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14201 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14201 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14215 =
                                               let uu____14216 =
                                                 let uu____14220 =
                                                   let uu____14221 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14221 in
                                                 (uu____14220,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14216 in
                                             [uu____14215]
                                           else [] in
                                         let uu____14224 =
                                           let uu____14226 =
                                             let uu____14228 =
                                               let uu____14229 =
                                                 let uu____14233 =
                                                   let uu____14234 =
                                                     let uu____14240 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14240) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14234 in
                                                 (uu____14233, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14229 in
                                             [uu____14228] in
                                           FStar_List.append karr uu____14226 in
                                         FStar_List.append decls1 uu____14224 in
                                   let aux =
                                     let uu____14249 =
                                       let uu____14251 =
                                         inversion_axioms tapp vars in
                                       let uu____14253 =
                                         let uu____14255 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14255] in
                                       FStar_List.append uu____14251
                                         uu____14253 in
                                     FStar_List.append kindingAx uu____14249 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14260,uu____14261,uu____14262,uu____14263,uu____14264,uu____14265)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14272,t,uu____14274,n_tps,quals,uu____14277) ->
          let uu____14282 = new_term_constant_and_tok_from_lid env d in
          (match uu____14282 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14293 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14293 with
                | (formals,t_res) ->
                    let uu____14315 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14315 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14324 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14324 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14362 =
                                            mk_term_projector_name d x in
                                          (uu____14362,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14364 =
                                  let uu____14374 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14374, true) in
                                FStar_All.pipe_right uu____14364
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
                              let uu____14396 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14396 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14404::uu____14405 ->
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
                                         let uu____14430 =
                                           let uu____14436 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14436) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14430
                                     | uu____14449 -> tok_typing in
                                   let uu____14454 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14454 with
                                    | (vars',guards',env'',decls_formals,uu____14469)
                                        ->
                                        let uu____14476 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14476 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14495 ->
                                                   let uu____14499 =
                                                     let uu____14500 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14500 in
                                                   [uu____14499] in
                                             let encode_elim uu____14507 =
                                               let uu____14508 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14508 with
                                               | (head1,args) ->
                                                   let uu____14537 =
                                                     let uu____14538 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14538.FStar_Syntax_Syntax.n in
                                                   (match uu____14537 with
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
                                                        let uu____14556 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14556
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
                                                                 | uu____14582
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14590
                                                                    =
                                                                    let uu____14591
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14591 in
                                                                    if
                                                                    uu____14590
                                                                    then
                                                                    let uu____14598
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14598]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14600
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14613
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14613
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14635
                                                                    =
                                                                    let uu____14639
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14639 in
                                                                    (match uu____14635
                                                                    with
                                                                    | 
                                                                    (uu____14646,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14652
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14652
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14654
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14654
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
                                                             (match uu____14600
                                                              with
                                                              | (uu____14662,arg_vars,elim_eqns_or_guards,uu____14665)
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
                                                                    let uu____14684
                                                                    =
                                                                    let uu____14688
                                                                    =
                                                                    let uu____14689
                                                                    =
                                                                    let uu____14695
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14701
                                                                    =
                                                                    let uu____14702
                                                                    =
                                                                    let uu____14705
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14705) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14702 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14695,
                                                                    uu____14701) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14689 in
                                                                    (uu____14688,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14684 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14718
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14718,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14720
                                                                    =
                                                                    let uu____14724
                                                                    =
                                                                    let uu____14725
                                                                    =
                                                                    let uu____14731
                                                                    =
                                                                    let uu____14734
                                                                    =
                                                                    let uu____14736
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14736] in
                                                                    [uu____14734] in
                                                                    let uu____14739
                                                                    =
                                                                    let uu____14740
                                                                    =
                                                                    let uu____14743
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14744
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14743,
                                                                    uu____14744) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14740 in
                                                                    (uu____14731,
                                                                    [x],
                                                                    uu____14739) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14725 in
                                                                    let uu____14754
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14724,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14754) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14720
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14759
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
                                                                    (let uu____14774
                                                                    =
                                                                    let uu____14775
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14775
                                                                    dapp1 in
                                                                    [uu____14774]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14759
                                                                    FStar_List.flatten in
                                                                    let uu____14779
                                                                    =
                                                                    let uu____14783
                                                                    =
                                                                    let uu____14784
                                                                    =
                                                                    let uu____14790
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14796
                                                                    =
                                                                    let uu____14797
                                                                    =
                                                                    let uu____14800
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14800) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14797 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14790,
                                                                    uu____14796) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14784 in
                                                                    (uu____14783,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14779) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14810 ->
                                                        ((let uu____14812 =
                                                            let uu____14813 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14814 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14813
                                                              uu____14814 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14812);
                                                         ([], []))) in
                                             let uu____14817 = encode_elim () in
                                             (match uu____14817 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14829 =
                                                      let uu____14831 =
                                                        let uu____14833 =
                                                          let uu____14835 =
                                                            let uu____14837 =
                                                              let uu____14838
                                                                =
                                                                let uu____14844
                                                                  =
                                                                  let uu____14846
                                                                    =
                                                                    let uu____14847
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14847 in
                                                                  Some
                                                                    uu____14846 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14844) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14838 in
                                                            [uu____14837] in
                                                          let uu____14850 =
                                                            let uu____14852 =
                                                              let uu____14854
                                                                =
                                                                let uu____14856
                                                                  =
                                                                  let uu____14858
                                                                    =
                                                                    let uu____14860
                                                                    =
                                                                    let uu____14862
                                                                    =
                                                                    let uu____14863
                                                                    =
                                                                    let uu____14867
                                                                    =
                                                                    let uu____14868
                                                                    =
                                                                    let uu____14874
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14874) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14868 in
                                                                    (uu____14867,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14863 in
                                                                    let uu____14881
                                                                    =
                                                                    let uu____14883
                                                                    =
                                                                    let uu____14884
                                                                    =
                                                                    let uu____14888
                                                                    =
                                                                    let uu____14889
                                                                    =
                                                                    let uu____14895
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14901
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14895,
                                                                    uu____14901) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14889 in
                                                                    (uu____14888,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14884 in
                                                                    [uu____14883] in
                                                                    uu____14862
                                                                    ::
                                                                    uu____14881 in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14860 in
                                                                  FStar_List.append
                                                                    uu____14858
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14856 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14854 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14852 in
                                                          FStar_List.append
                                                            uu____14835
                                                            uu____14850 in
                                                        FStar_List.append
                                                          decls3 uu____14833 in
                                                      FStar_List.append
                                                        decls2 uu____14831 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14829 in
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
           (fun uu____14922  ->
              fun se  ->
                match uu____14922 with
                | (g,env1) ->
                    let uu____14934 = encode_sigelt env1 se in
                    (match uu____14934 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14970 =
        match uu____14970 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14988 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14993 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14993
                   then
                     let uu____14994 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14995 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14996 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14994 uu____14995 uu____14996
                   else ());
                  (let uu____14998 = encode_term t1 env1 in
                   match uu____14998 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15008 =
                         let uu____15012 =
                           let uu____15013 =
                             let uu____15014 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15014
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15013 in
                         new_term_constant_from_string env1 x uu____15012 in
                       (match uu____15008 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15025 = FStar_Options.log_queries () in
                              if uu____15025
                              then
                                let uu____15027 =
                                  let uu____15028 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15029 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15030 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15028 uu____15029 uu____15030 in
                                Some uu____15027
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15041,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15050 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15050 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____15069 = encode_sigelt env1 se in
                 (match uu____15069 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15079 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15079 with | (uu____15091,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15136  ->
            match uu____15136 with
            | (l,uu____15143,uu____15144) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15165  ->
            match uu____15165 with
            | (l,uu____15173,uu____15174) ->
                let uu____15179 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____15180 =
                  let uu____15182 =
                    let uu____15183 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15183 in
                  [uu____15182] in
                uu____15179 :: uu____15180)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15194 =
      let uu____15196 =
        let uu____15197 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15209 =
          let uu____15210 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15210 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15197;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15209
        } in
      [uu____15196] in
    FStar_ST.write last_env uu____15194
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15220 = FStar_ST.read last_env in
      match uu____15220 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15226 ->
          let uu___161_15228 = e in
          let uu____15229 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___161_15228.bindings);
            depth = (uu___161_15228.depth);
            tcenv;
            warn = (uu___161_15228.warn);
            cache = (uu___161_15228.cache);
            nolabels = (uu___161_15228.nolabels);
            use_zfuel_name = (uu___161_15228.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___161_15228.encode_non_total_function_typ);
            current_module_name = uu____15229
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15233 = FStar_ST.read last_env in
    match uu____15233 with
    | [] -> failwith "Empty env stack"
    | uu____15238::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15246  ->
    let uu____15247 = FStar_ST.read last_env in
    match uu____15247 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___162_15268 = hd1 in
          {
            bindings = (uu___162_15268.bindings);
            depth = (uu___162_15268.depth);
            tcenv = (uu___162_15268.tcenv);
            warn = (uu___162_15268.warn);
            cache = refs;
            nolabels = (uu___162_15268.nolabels);
            use_zfuel_name = (uu___162_15268.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_15268.encode_non_total_function_typ);
            current_module_name = (uu___162_15268.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15274  ->
    let uu____15275 = FStar_ST.read last_env in
    match uu____15275 with
    | [] -> failwith "Popping an empty stack"
    | uu____15280::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15288  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15291  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15294  ->
    let uu____15295 = FStar_ST.read last_env in
    match uu____15295 with
    | hd1::uu____15301::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15307 -> failwith "Impossible"
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
        let uu____15352 = FStar_Options.log_queries () in
        if uu____15352
        then
          let uu____15354 =
            let uu____15355 =
              let uu____15356 =
                let uu____15357 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15357 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15356 in
            FStar_SMTEncoding_Term.Caption uu____15355 in
          uu____15354 :: decls
        else decls in
      let env =
        let uu____15364 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15364 tcenv in
      let uu____15365 = encode_sigelt env se in
      match uu____15365 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15371 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15371))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15382 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15382
       then
         let uu____15383 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15383
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let uu____15388 =
         encode_signature
           (let uu___163_15392 = env in
            {
              bindings = (uu___163_15392.bindings);
              depth = (uu___163_15392.depth);
              tcenv = (uu___163_15392.tcenv);
              warn = false;
              cache = (uu___163_15392.cache);
              nolabels = (uu___163_15392.nolabels);
              use_zfuel_name = (uu___163_15392.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___163_15392.encode_non_total_function_typ);
              current_module_name = (uu___163_15392.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15388 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15404 = FStar_Options.log_queries () in
             if uu____15404
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___164_15409 = env1 in
               {
                 bindings = (uu___164_15409.bindings);
                 depth = (uu___164_15409.depth);
                 tcenv = (uu___164_15409.tcenv);
                 warn = true;
                 cache = (uu___164_15409.cache);
                 nolabels = (uu___164_15409.nolabels);
                 use_zfuel_name = (uu___164_15409.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___164_15409.encode_non_total_function_typ);
                 current_module_name = (uu___164_15409.current_module_name)
               });
            (let uu____15411 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15411
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
        (let uu____15446 =
           let uu____15447 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15447.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15446);
        (let env =
           let uu____15449 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15449 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15456 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15477 = aux rest in
                 (match uu____15477 with
                  | (out,rest1) ->
                      let t =
                        let uu____15495 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15495 with
                        | Some uu____15499 ->
                            let uu____15500 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15500
                              x.FStar_Syntax_Syntax.sort
                        | uu____15501 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15504 =
                        let uu____15506 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___165_15507 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___165_15507.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___165_15507.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15506 :: out in
                      (uu____15504, rest1))
             | uu____15510 -> ([], bindings1) in
           let uu____15514 = aux bindings in
           match uu____15514 with
           | (closing,bindings1) ->
               let uu____15528 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15528, bindings1) in
         match uu____15456 with
         | (q1,bindings1) ->
             let uu____15541 =
               let uu____15544 =
                 FStar_List.filter
                   (fun uu___134_15546  ->
                      match uu___134_15546 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15547 ->
                          false
                      | uu____15551 -> true) bindings1 in
               encode_env_bindings env uu____15544 in
             (match uu____15541 with
              | (env_decls,env1) ->
                  ((let uu____15562 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15562
                    then
                      let uu____15563 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15563
                    else ());
                   (let uu____15565 = encode_formula q1 env1 in
                    match uu____15565 with
                    | (phi,qdecls) ->
                        let uu____15577 =
                          let uu____15580 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15580 phi in
                        (match uu____15577 with
                         | (labels,phi1) ->
                             let uu____15590 = encode_labels labels in
                             (match uu____15590 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15611 =
                                      let uu____15615 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15616 =
                                        varops.mk_unique "@query" in
                                      (uu____15615, (Some "query"),
                                        uu____15616) in
                                    FStar_SMTEncoding_Term.Assume uu____15611 in
                                  let suffix =
                                    let uu____15620 =
                                      let uu____15622 =
                                        let uu____15624 =
                                          FStar_Options.print_z3_statistics
                                            () in
                                        if uu____15624
                                        then
                                          [FStar_SMTEncoding_Term.PrintStats]
                                        else [] in
                                      FStar_List.append uu____15622
                                        [FStar_SMTEncoding_Term.Echo "Done!"] in
                                    FStar_List.append label_suffix
                                      uu____15620 in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15636 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15636 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15638 = encode_formula q env in
       match uu____15638 with
       | (f,uu____15642) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15644) -> true
             | uu____15647 -> false)))