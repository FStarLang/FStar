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
      let uu____1725 = FStar_Syntax_Syntax.null_binder t in [uu____1725] in
    let uu____1726 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1724 uu____1726 None
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
                    let uu____1753 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1753
                | s ->
                    let uu____1756 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1756) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___118_1768  ->
    match uu___118_1768 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1769 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____1797;
                       FStar_SMTEncoding_Term.rng = uu____1798;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (uu____1810,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1813 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1815 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1815)) in
              if uu____1813 then Some t else None
          | uu____1818 -> None in
        match body.FStar_SMTEncoding_Term.tm with
        | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var f,args) ->
            let uu____1827 =
              ((FStar_List.length args) = (FStar_List.length vars)) &&
                (FStar_List.forall2
                   (fun a  ->
                      fun v1  ->
                        match a.FStar_SMTEncoding_Term.tm with
                        | FStar_SMTEncoding_Term.FreeV fv ->
                            FStar_SMTEncoding_Term.fv_eq fv v1
                        | uu____1837 -> false) args vars) in
            if uu____1827 then tok_of_name env f 
            else check_partial_applications body (FStar_List.rev vars)
        | uu____1840 -> check_partial_applications body (FStar_List.rev vars)
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
      (let uu____1852 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____1852
       then
         let uu____1853 = FStar_Syntax_Print.term_to_string tm in
         let uu____1854 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____1853 uu____1854
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
    | uu____1936 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___119_1939  ->
    match uu___119_1939 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____1941 =
          let uu____1945 =
            let uu____1947 =
              let uu____1948 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____1948 in
            [uu____1947] in
          ("FStar.Char.Char", uu____1945) in
        FStar_SMTEncoding_Util.mkApp uu____1941
    | FStar_Const.Const_int (i,None ) ->
        let uu____1956 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____1956
    | FStar_Const.Const_int (i,Some uu____1958) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____1967) ->
        let uu____1970 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____1970
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____1974 =
          let uu____1975 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____1975 in
        failwith uu____1974
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1994 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2002 ->
            let uu____2007 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2007
        | uu____2008 ->
            if norm1
            then let uu____2009 = whnf env t1 in aux false uu____2009
            else
              (let uu____2011 =
                 let uu____2012 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2013 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2012 uu____2013 in
               failwith uu____2011) in
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
    | uu____2034 ->
        let uu____2035 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2035)
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
        (let uu____2178 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2178
         then
           let uu____2179 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2179
         else ());
        (let uu____2181 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2217  ->
                   fun b  ->
                     match uu____2217 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2260 =
                           let x = unmangle (Prims.fst b) in
                           let uu____2269 = gen_term_var env1 x in
                           match uu____2269 with
                           | (xxsym,xx,env') ->
                               let uu____2283 =
                                 let uu____2286 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2286 env1 xx in
                               (match uu____2283 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2260 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2181 with
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
          let uu____2374 = encode_term t env in
          match uu____2374 with
          | (t1,decls) ->
              let uu____2381 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2381, decls)
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
          let uu____2389 = encode_term t env in
          match uu____2389 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2398 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2398, decls)
               | Some f ->
                   let uu____2400 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2400, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2407 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2407
       then
         let uu____2408 = FStar_Syntax_Print.tag_of_term t in
         let uu____2409 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2410 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2408 uu____2409
           uu____2410
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2415 =
             let uu____2416 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2417 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2418 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2419 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2416
               uu____2417 uu____2418 uu____2419 in
           failwith uu____2415
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2423 =
             let uu____2424 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2424 in
           failwith uu____2423
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2429) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2459) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2468 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2468, [])
       | FStar_Syntax_Syntax.Tm_type uu____2474 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2477) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2483 = encode_const c in (uu____2483, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2498 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2498 with
            | (binders1,res) ->
                let uu____2505 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2505
                then
                  let uu____2508 = encode_binders None binders1 env in
                  (match uu____2508 with
                   | (vars,guards,env',decls,uu____2523) ->
                       let fsym =
                         let uu____2533 = varops.fresh "f" in
                         (uu____2533, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2536 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___144_2540 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___144_2540.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___144_2540.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___144_2540.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___144_2540.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___144_2540.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___144_2540.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___144_2540.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___144_2540.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___144_2540.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___144_2540.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___144_2540.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___144_2540.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___144_2540.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___144_2540.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___144_2540.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___144_2540.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___144_2540.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___144_2540.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___144_2540.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___144_2540.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___144_2540.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___144_2540.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___144_2540.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2536 with
                        | (pre_opt,res_t) ->
                            let uu____2547 =
                              encode_term_pred None res_t env' app in
                            (match uu____2547 with
                             | (res_pred,decls') ->
                                 let uu____2554 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2561 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2561, [])
                                   | Some pre ->
                                       let uu____2564 =
                                         encode_formula pre env' in
                                       (match uu____2564 with
                                        | (guard,decls0) ->
                                            let uu____2572 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2572, decls0)) in
                                 (match uu____2554 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2580 =
                                          let uu____2586 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2586) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2580 in
                                      let cvars =
                                        let uu____2596 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2596
                                          (FStar_List.filter
                                             (fun uu____2602  ->
                                                match uu____2602 with
                                                | (x,uu____2606) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2617 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2617 with
                                       | Some (t',sorts,uu____2633) ->
                                           let uu____2643 =
                                             let uu____2644 =
                                               let uu____2648 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               (t', uu____2648) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2644 in
                                           (uu____2643, [])
                                       | None  ->
                                           let tsym =
                                             let uu____2664 =
                                               let uu____2665 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2665 in
                                             varops.mk_unique uu____2664 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2672 =
                                               FStar_Options.log_queries () in
                                             if uu____2672
                                             then
                                               let uu____2674 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2674
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2680 =
                                               let uu____2684 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2684) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2680 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____2692 =
                                               let uu____2696 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2696, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2692 in
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
                                             let uu____2709 =
                                               let uu____2713 =
                                                 let uu____2714 =
                                                   let uu____2720 =
                                                     let uu____2721 =
                                                       let uu____2724 =
                                                         let uu____2725 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2725 in
                                                       (f_has_t, uu____2724) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2721 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2720) in
                                                 mkForall_fuel uu____2714 in
                                               (uu____2713,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2709 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____2738 =
                                               let uu____2742 =
                                                 let uu____2743 =
                                                   let uu____2749 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2749) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2743 in
                                               (uu____2742, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2738 in
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
                     let uu____2780 =
                       let uu____2784 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____2784, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Term.Assume uu____2780 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____2793 =
                       let uu____2797 =
                         let uu____2798 =
                           let uu____2804 =
                             let uu____2805 =
                               let uu____2808 =
                                 let uu____2809 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2809 in
                               (f_has_t, uu____2808) in
                             FStar_SMTEncoding_Util.mkImp uu____2805 in
                           ([[f_has_t]], [fsym], uu____2804) in
                         mkForall_fuel uu____2798 in
                       (uu____2797, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Term.Assume uu____2793 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2823 ->
           let uu____2828 =
             let uu____2831 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2831 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2836;
                 FStar_Syntax_Syntax.pos = uu____2837;
                 FStar_Syntax_Syntax.vars = uu____2838;_} ->
                 let uu____2845 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2845 with
                  | (b,f1) ->
                      let uu____2859 =
                        let uu____2860 = FStar_List.hd b in
                        Prims.fst uu____2860 in
                      (uu____2859, f1))
             | uu____2865 -> failwith "impossible" in
           (match uu____2828 with
            | (x,f) ->
                let uu____2872 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____2872 with
                 | (base_t,decls) ->
                     let uu____2879 = gen_term_var env x in
                     (match uu____2879 with
                      | (x1,xtm,env') ->
                          let uu____2888 = encode_formula f env' in
                          (match uu____2888 with
                           | (refinement,decls') ->
                               let uu____2895 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____2895 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____2906 =
                                        let uu____2908 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____2912 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____2908
                                          uu____2912 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____2906 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____2928  ->
                                              match uu____2928 with
                                              | (y,uu____2932) ->
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
                                    let uu____2951 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2951 with
                                     | Some (t1,uu____2966,uu____2967) ->
                                         let uu____2977 =
                                           let uu____2978 =
                                             let uu____2982 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             (t1, uu____2982) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2978 in
                                         (uu____2977, [])
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____2999 =
                                             let uu____3000 =
                                               let uu____3001 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3001 in
                                             Prims.strcat module_name
                                               uu____3000 in
                                           varops.mk_unique uu____2999 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3010 =
                                             let uu____3014 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3014) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3010 in
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
                                           let uu____3024 =
                                             let uu____3028 =
                                               let uu____3029 =
                                                 let uu____3035 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3035) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3029 in
                                             (uu____3028,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3024 in
                                         let t_kinding =
                                           let uu____3045 =
                                             let uu____3049 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3049,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3045 in
                                         let t_interp =
                                           let uu____3059 =
                                             let uu____3063 =
                                               let uu____3064 =
                                                 let uu____3070 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3070) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3064 in
                                             let uu____3082 =
                                               let uu____3084 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3084 in
                                             (uu____3063, uu____3082,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3059 in
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
             let uu____3112 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3112 in
           let uu____3116 = encode_term_pred None k env ttm in
           (match uu____3116 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3124 =
                    let uu____3128 =
                      let uu____3129 =
                        let uu____3130 =
                          let uu____3131 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3131 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3130 in
                      varops.mk_unique uu____3129 in
                    (t_has_k, (Some "Uvar typing"), uu____3128) in
                  FStar_SMTEncoding_Term.Assume uu____3124 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3137 ->
           let uu____3147 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3147 with
            | (head1,args_e) ->
                let uu____3175 =
                  let uu____3183 =
                    let uu____3184 = FStar_Syntax_Subst.compress head1 in
                    uu____3184.FStar_Syntax_Syntax.n in
                  (uu____3183, args_e) in
                (match uu____3175 with
                 | (uu____3194,uu____3195) when head_redex env head1 ->
                     let uu____3206 = whnf env t in
                     encode_term uu____3206 env
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
                     let uu____3280 = encode_term v1 env in
                     (match uu____3280 with
                      | (v11,decls1) ->
                          let uu____3287 = encode_term v2 env in
                          (match uu____3287 with
                           | (v21,decls2) ->
                               let uu____3294 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3294,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3296) ->
                     let e0 =
                       let uu____3310 =
                         let uu____3313 =
                           let uu____3314 =
                             let uu____3324 =
                               let uu____3330 = FStar_List.hd args_e in
                               [uu____3330] in
                             (head1, uu____3324) in
                           FStar_Syntax_Syntax.Tm_app uu____3314 in
                         FStar_Syntax_Syntax.mk uu____3313 in
                       uu____3310 None head1.FStar_Syntax_Syntax.pos in
                     ((let uu____3363 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3363
                       then
                         let uu____3364 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Trying to normalize %s\n"
                           uu____3364
                       else ());
                      (let e01 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Reify;
                           FStar_TypeChecker_Normalize.Eager_unfolding;
                           FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                           env.tcenv e0 in
                       (let uu____3368 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify") in
                        if uu____3368
                        then
                          let uu____3369 =
                            FStar_Syntax_Print.term_to_string e01 in
                          FStar_Util.print1 "Result of normalization %s\n"
                            uu____3369
                        else ());
                       (let e02 =
                          let uu____3372 =
                            let uu____3373 =
                              let uu____3374 =
                                FStar_Syntax_Subst.compress e01 in
                              uu____3374.FStar_Syntax_Syntax.n in
                            match uu____3373 with
                            | FStar_Syntax_Syntax.Tm_app uu____3377 -> false
                            | uu____3387 -> true in
                          if uu____3372
                          then e01
                          else
                            (let uu____3389 =
                               FStar_Syntax_Util.head_and_args e01 in
                             match uu____3389 with
                             | (head2,args) ->
                                 let uu____3415 =
                                   let uu____3416 =
                                     let uu____3417 =
                                       FStar_Syntax_Subst.compress head2 in
                                     uu____3417.FStar_Syntax_Syntax.n in
                                   match uu____3416 with
                                   | FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_reify ) -> true
                                   | uu____3420 -> false in
                                 if uu____3415
                                 then
                                   (match args with
                                    | x::[] -> Prims.fst x
                                    | uu____3436 ->
                                        failwith
                                          "Impossible : Reify applied to multiple arguments after normalization.")
                                 else e01) in
                        let e =
                          match args_e with
                          | uu____3444::[] -> e02
                          | uu____3457 ->
                              let uu____3463 =
                                let uu____3466 =
                                  let uu____3467 =
                                    let uu____3477 = FStar_List.tl args_e in
                                    (e02, uu____3477) in
                                  FStar_Syntax_Syntax.Tm_app uu____3467 in
                                FStar_Syntax_Syntax.mk uu____3466 in
                              uu____3463 None t0.FStar_Syntax_Syntax.pos in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3500),(arg,uu____3502)::[]) -> encode_term arg env
                 | uu____3520 ->
                     let uu____3528 = encode_args args_e env in
                     (match uu____3528 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3561 = encode_term head1 env in
                            match uu____3561 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3600 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3600 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3642  ->
                                                 fun uu____3643  ->
                                                   match (uu____3642,
                                                           uu____3643)
                                                   with
                                                   | ((bv,uu____3657),
                                                      (a,uu____3659)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3673 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3673
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3678 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3678 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3688 =
                                                   let uu____3692 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3697 =
                                                     let uu____3698 =
                                                       let uu____3699 =
                                                         let uu____3700 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3700 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3699 in
                                                     varops.mk_unique
                                                       uu____3698 in
                                                   (uu____3692,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3697) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3688 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3717 = lookup_free_var_sym env fv in
                            match uu____3717 with
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
                                let uu____3755 =
                                  let uu____3756 =
                                    let uu____3759 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3759 Prims.fst in
                                  FStar_All.pipe_right uu____3756 Prims.snd in
                                Some uu____3755
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3778,(FStar_Util.Inl t1,uu____3780),uu____3781)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3819,(FStar_Util.Inr c,uu____3821),uu____3822)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3860 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3880 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3880 in
                               let uu____3881 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3881 with
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
                                     | uu____3906 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3951 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3951 with
            | (bs1,body1,opening) ->
                let fallback uu____3966 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3971 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3971, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3982 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3982
                  | FStar_Util.Inr (eff,uu____3984) ->
                      let uu____3990 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3990 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body = reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4035 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___145_4036 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___145_4036.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___145_4036.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___145_4036.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___145_4036.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___145_4036.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___145_4036.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___145_4036.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___145_4036.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___145_4036.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___145_4036.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___145_4036.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___145_4036.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___145_4036.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___145_4036.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___145_4036.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___145_4036.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___145_4036.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___145_4036.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___145_4036.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___145_4036.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___145_4036.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___145_4036.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___145_4036.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4035 FStar_Syntax_Syntax.U_unknown in
                        let uu____4037 =
                          let uu____4038 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4038 in
                        FStar_Util.Inl uu____4037
                    | FStar_Util.Inr (eff_name,uu____4045) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4076 =
                        let uu____4077 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4077 in
                      FStar_All.pipe_right uu____4076
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4089 =
                        let uu____4090 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4090 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4098 =
                          let uu____4099 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4099 in
                        FStar_All.pipe_right uu____4098
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4103 =
                             let uu____4104 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4104 in
                           FStar_All.pipe_right uu____4103
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4115 =
                         let uu____4116 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4116 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4115);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4131 =
                       (is_impure lc1) &&
                         (let uu____4132 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4132) in
                     if uu____4131
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4142 = encode_binders None bs1 env in
                        match uu____4142 with
                        | (vars,guards,envbody,decls,uu____4157) ->
                            let uu____4164 =
                              let uu____4172 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4172
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4164 with
                             | (lc2,body2) ->
                                 let uu____4197 = encode_term body2 envbody in
                                 (match uu____4197 with
                                  | (body3,decls') ->
                                      let uu____4204 =
                                        let uu____4209 = codomain_eff lc2 in
                                        match uu____4209 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4221 =
                                              encode_term tfun env in
                                            (match uu____4221 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4204 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4240 =
                                               let uu____4246 =
                                                 let uu____4247 =
                                                   let uu____4250 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4250, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4247 in
                                               ([], vars, uu____4246) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4240 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4258 =
                                                   let uu____4260 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4260 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4258 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4271 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4271 with
                                            | Some (t1,uu____4286,uu____4287)
                                                ->
                                                let uu____4297 =
                                                  let uu____4298 =
                                                    let uu____4302 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (t1, uu____4302) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4298 in
                                                (uu____4297, [])
                                            | None  ->
                                                let uu____4313 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4313 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4320 =
                                                         let uu____4321 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4321 =
                                                           cache_size in
                                                       if uu____4320
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
                                                         let uu____4337 =
                                                           let uu____4338 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4338 in
                                                         varops.mk_unique
                                                           uu____4337 in
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
                                                       let uu____4343 =
                                                         let uu____4347 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4347) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4343 in
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
                                                           let uu____4359 =
                                                             let uu____4360 =
                                                               let uu____4364
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4364,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____4360 in
                                                           [uu____4359] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4372 =
                                                         let uu____4376 =
                                                           let uu____4377 =
                                                             let uu____4383 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4383) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4377 in
                                                         (uu____4376,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Term.Assume
                                                         uu____4372 in
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
                                                        (fsym, cvar_sorts,
                                                          f_decls);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4401,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4402;
                          FStar_Syntax_Syntax.lbunivs = uu____4403;
                          FStar_Syntax_Syntax.lbtyp = uu____4404;
                          FStar_Syntax_Syntax.lbeff = uu____4405;
                          FStar_Syntax_Syntax.lbdef = uu____4406;_}::uu____4407),uu____4408)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4426;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4428;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4444 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4457 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4457, [decl_e])))
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
              let uu____4499 = encode_term e1 env in
              match uu____4499 with
              | (ee1,decls1) ->
                  let uu____4506 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4506 with
                   | (xs,e21) ->
                       let uu____4520 = FStar_List.hd xs in
                       (match uu____4520 with
                        | (x1,uu____4528) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4530 = encode_body e21 env' in
                            (match uu____4530 with
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
            let uu____4552 =
              let uu____4556 =
                let uu____4557 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4557 in
              gen_term_var env uu____4556 in
            match uu____4552 with
            | (scrsym,scr',env1) ->
                let uu____4571 = encode_term e env1 in
                (match uu____4571 with
                 | (scr,decls) ->
                     let uu____4578 =
                       let encode_branch b uu____4594 =
                         match uu____4594 with
                         | (else_case,decls1) ->
                             let uu____4605 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4605 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4635  ->
                                       fun uu____4636  ->
                                         match (uu____4635, uu____4636) with
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
                                                       fun uu____4673  ->
                                                         match uu____4673
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4678 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4693 =
                                                     encode_term w1 env2 in
                                                   (match uu____4693 with
                                                    | (w2,decls21) ->
                                                        let uu____4701 =
                                                          let uu____4702 =
                                                            let uu____4705 =
                                                              let uu____4706
                                                                =
                                                                let uu____4709
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4709) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4706 in
                                                            (guard,
                                                              uu____4705) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4702 in
                                                        (uu____4701, decls21)) in
                                             (match uu____4678 with
                                              | (guard1,decls21) ->
                                                  let uu____4717 =
                                                    encode_br br env2 in
                                                  (match uu____4717 with
                                                   | (br1,decls3) ->
                                                       let uu____4725 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4725,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4578 with
                      | (match_tm,decls1) ->
                          let uu____4737 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4737, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4768 -> let uu____4769 = encode_one_pat env pat in [uu____4769]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4781 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4781
       then
         let uu____4782 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4782
       else ());
      (let uu____4784 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4784 with
       | (vars,pat_term) ->
           let uu____4794 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4817  ->
                     fun v1  ->
                       match uu____4817 with
                       | (env1,vars1) ->
                           let uu____4845 = gen_term_var env1 v1 in
                           (match uu____4845 with
                            | (xx,uu____4857,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4794 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4904 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4912 =
                        let uu____4915 = encode_const c in
                        (scrutinee, uu____4915) in
                      FStar_SMTEncoding_Util.mkEq uu____4912
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4934 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4934 with
                        | (uu____4938,uu____4939::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4941 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4962  ->
                                  match uu____4962 with
                                  | (arg,uu____4968) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4978 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4978)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4997 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5012 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5027 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5049  ->
                                  match uu____5049 with
                                  | (arg,uu____5058) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5068 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5068)) in
                      FStar_All.pipe_right uu____5027 FStar_List.flatten in
                let pat_term1 uu____5084 = encode_term pat_term env1 in
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
      let uu____5091 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5106  ->
                fun uu____5107  ->
                  match (uu____5106, uu____5107) with
                  | ((tms,decls),(t,uu____5127)) ->
                      let uu____5138 = encode_term t env in
                      (match uu____5138 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5091 with | (l1,decls) -> ((FStar_List.rev l1), decls)
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
            let uu____5176 = FStar_Syntax_Util.list_elements e in
            match uu____5176 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 []) in
          let one_pat p =
            let uu____5194 =
              let uu____5204 = FStar_Syntax_Util.unmeta p in
              FStar_All.pipe_right uu____5204 FStar_Syntax_Util.head_and_args in
            match uu____5194 with
            | (head1,args) ->
                let uu____5235 =
                  let uu____5243 =
                    let uu____5244 = FStar_Syntax_Util.un_uinst head1 in
                    uu____5244.FStar_Syntax_Syntax.n in
                  (uu____5243, args) in
                (match uu____5235 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5258,uu____5259)::(e,uu____5261)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5292)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5313 -> failwith "Unexpected pattern term") in
          let lemma_pats p =
            let elts = list_elements1 p in
            let smt_pat_or t1 =
              let uu____5346 =
                let uu____5356 = FStar_Syntax_Util.unmeta t1 in
                FStar_All.pipe_right uu____5356
                  FStar_Syntax_Util.head_and_args in
              match uu____5346 with
              | (head1,args) ->
                  let uu____5385 =
                    let uu____5393 =
                      let uu____5394 = FStar_Syntax_Util.un_uinst head1 in
                      uu____5394.FStar_Syntax_Syntax.n in
                    (uu____5393, args) in
                  (match uu____5385 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5407)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5427 -> None) in
            match elts with
            | t1::[] ->
                let uu____5445 = smt_pat_or t1 in
                (match uu____5445 with
                 | Some e ->
                     let uu____5461 = list_elements1 e in
                     FStar_All.pipe_right uu____5461
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5478 = list_elements1 branch1 in
                             FStar_All.pipe_right uu____5478
                               (FStar_List.map one_pat)))
                 | uu____5492 ->
                     let uu____5496 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat) in
                     [uu____5496])
            | uu____5527 ->
                let uu____5529 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat) in
                [uu____5529] in
          let uu____5560 =
            let uu____5576 =
              let uu____5577 = FStar_Syntax_Subst.compress t in
              uu____5577.FStar_Syntax_Syntax.n in
            match uu____5576 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5607 = FStar_Syntax_Subst.open_comp binders c in
                (match uu____5607 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5642;
                            FStar_Syntax_Syntax.effect_name = uu____5643;
                            FStar_Syntax_Syntax.result_typ = uu____5644;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5646)::(post,uu____5648)::(pats,uu____5650)::[];
                            FStar_Syntax_Syntax.flags = uu____5651;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats in
                          let uu____5685 = lemma_pats pats' in
                          (binders1, pre, post, uu____5685)
                      | uu____5704 -> failwith "impos"))
            | uu____5720 -> failwith "Impos" in
          match uu____5560 with
          | (binders,pre,post,patterns) ->
              let uu____5764 = encode_binders None binders env in
              (match uu____5764 with
               | (vars,guards,env1,decls,uu____5779) ->
                   let uu____5786 =
                     let uu____5793 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5824 =
                                 let uu____5829 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5845  ->
                                           match uu____5845 with
                                           | (t1,uu____5852) ->
                                               encode_term t1
                                                 (let uu___146_5855 = env1 in
                                                  {
                                                    bindings =
                                                      (uu___146_5855.bindings);
                                                    depth =
                                                      (uu___146_5855.depth);
                                                    tcenv =
                                                      (uu___146_5855.tcenv);
                                                    warn =
                                                      (uu___146_5855.warn);
                                                    cache =
                                                      (uu___146_5855.cache);
                                                    nolabels =
                                                      (uu___146_5855.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___146_5855.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___146_5855.current_module_name)
                                                  }))) in
                                 FStar_All.pipe_right uu____5829
                                   FStar_List.unzip in
                               match uu____5824 with
                               | (pats,decls1) -> (pats, decls1))) in
                     FStar_All.pipe_right uu____5793 FStar_List.unzip in
                   (match uu____5786 with
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
                                           let uu____5919 =
                                             let uu____5920 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5920 e in
                                           uu____5919 :: p))
                               | uu____5921 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5950 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e in
                                                 uu____5950 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5958 =
                                           let uu____5959 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort) in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5959 tl1 in
                                         aux uu____5958 vars2
                                     | uu____5960 -> pats in
                                   let uu____5964 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort) in
                                   aux uu____5964 vars) in
                        let env2 =
                          let uu___147_5966 = env1 in
                          {
                            bindings = (uu___147_5966.bindings);
                            depth = (uu___147_5966.depth);
                            tcenv = (uu___147_5966.tcenv);
                            warn = (uu___147_5966.warn);
                            cache = (uu___147_5966.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___147_5966.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___147_5966.encode_non_total_function_typ);
                            current_module_name =
                              (uu___147_5966.current_module_name)
                          } in
                        let uu____5967 =
                          let uu____5970 = FStar_Syntax_Util.unmeta pre in
                          encode_formula uu____5970 env2 in
                        (match uu____5967 with
                         | (pre1,decls'') ->
                             let uu____5975 =
                               let uu____5978 = FStar_Syntax_Util.unmeta post in
                               encode_formula uu____5978 env2 in
                             (match uu____5975 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls''')) in
                                  let uu____5985 =
                                    let uu____5986 =
                                      let uu____5992 =
                                        let uu____5993 =
                                          let uu____5996 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards) in
                                          (uu____5996, post1) in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5993 in
                                      (pats1, vars, uu____5992) in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5986 in
                                  (uu____5985, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6009 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6009
        then
          let uu____6010 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6011 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6010 uu____6011
        else () in
      let enc f r l =
        let uu____6038 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6051 = encode_term (Prims.fst x) env in
                 match uu____6051 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6038 with
        | (decls,args) ->
            let uu____6068 =
              let uu___148_6069 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___148_6069.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___148_6069.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6068, decls) in
      let const_op f r uu____6088 = let uu____6091 = f r in (uu____6091, []) in
      let un_op f l =
        let uu____6107 = FStar_List.hd l in FStar_All.pipe_left f uu____6107 in
      let bin_op f uu___120_6120 =
        match uu___120_6120 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6128 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6155 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6164  ->
                 match uu____6164 with
                 | (t,uu____6172) ->
                     let uu____6173 = encode_formula t env in
                     (match uu____6173 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6155 with
        | (decls,phis) ->
            let uu____6190 =
              let uu___149_6191 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___149_6191.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___149_6191.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6190, decls) in
      let eq_op r uu___121_6207 =
        match uu___121_6207 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6267 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6267 r [e1; e2]
        | l ->
            let uu____6287 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6287 r l in
      let mk_imp1 r uu___122_6306 =
        match uu___122_6306 with
        | (lhs,uu____6310)::(rhs,uu____6312)::[] ->
            let uu____6333 = encode_formula rhs env in
            (match uu____6333 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6342) ->
                      (l1, decls1)
                  | uu____6345 ->
                      let uu____6346 = encode_formula lhs env in
                      (match uu____6346 with
                       | (l2,decls2) ->
                           let uu____6353 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6353, (FStar_List.append decls1 decls2)))))
        | uu____6355 -> failwith "impossible" in
      let mk_ite r uu___123_6370 =
        match uu___123_6370 with
        | (guard,uu____6374)::(_then,uu____6376)::(_else,uu____6378)::[] ->
            let uu____6407 = encode_formula guard env in
            (match uu____6407 with
             | (g,decls1) ->
                 let uu____6414 = encode_formula _then env in
                 (match uu____6414 with
                  | (t,decls2) ->
                      let uu____6421 = encode_formula _else env in
                      (match uu____6421 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6430 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6449 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6449 in
      let connectives =
        let uu____6461 =
          let uu____6470 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6470) in
        let uu____6483 =
          let uu____6493 =
            let uu____6502 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6502) in
          let uu____6515 =
            let uu____6525 =
              let uu____6535 =
                let uu____6544 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6544) in
              let uu____6557 =
                let uu____6567 =
                  let uu____6577 =
                    let uu____6586 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6586) in
                  [uu____6577;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6567 in
              uu____6535 :: uu____6557 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6525 in
          uu____6493 :: uu____6515 in
        uu____6461 :: uu____6483 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6748 = encode_formula phi' env in
            (match uu____6748 with
             | (phi2,decls) ->
                 let uu____6755 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6755, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6756 ->
            let uu____6761 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6761 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6790 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6790 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6798;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6800;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6816 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6816 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6848::(x,uu____6850)::(t,uu____6852)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6886 = encode_term x env in
                 (match uu____6886 with
                  | (x1,decls) ->
                      let uu____6893 = encode_term t env in
                      (match uu____6893 with
                       | (t1,decls') ->
                           let uu____6900 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6900, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6904)::(msg,uu____6906)::(phi2,uu____6908)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6942 =
                   let uu____6945 =
                     let uu____6946 = FStar_Syntax_Subst.compress r in
                     uu____6946.FStar_Syntax_Syntax.n in
                   let uu____6949 =
                     let uu____6950 = FStar_Syntax_Subst.compress msg in
                     uu____6950.FStar_Syntax_Syntax.n in
                   (uu____6945, uu____6949) in
                 (match uu____6942 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6957))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6973 -> fallback phi2)
             | uu____6976 when head_redex env head2 ->
                 let uu____6984 = whnf env phi1 in
                 encode_formula uu____6984 env
             | uu____6985 ->
                 let uu____6993 = encode_term phi1 env in
                 (match uu____6993 with
                  | (tt,decls) ->
                      let uu____7000 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___150_7001 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___150_7001.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___150_7001.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7000, decls)))
        | uu____7004 ->
            let uu____7005 = encode_term phi1 env in
            (match uu____7005 with
             | (tt,decls) ->
                 let uu____7012 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___151_7013 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___151_7013.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___151_7013.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7012, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7040 = encode_binders None bs env1 in
        match uu____7040 with
        | (vars,guards,env2,decls,uu____7062) ->
            let uu____7069 =
              let uu____7076 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7099 =
                          let uu____7104 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7118  ->
                                    match uu____7118 with
                                    | (t,uu____7124) ->
                                        encode_term t
                                          (let uu___152_7125 = env2 in
                                           {
                                             bindings =
                                               (uu___152_7125.bindings);
                                             depth = (uu___152_7125.depth);
                                             tcenv = (uu___152_7125.tcenv);
                                             warn = (uu___152_7125.warn);
                                             cache = (uu___152_7125.cache);
                                             nolabels =
                                               (uu___152_7125.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___152_7125.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___152_7125.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7104 FStar_List.unzip in
                        match uu____7099 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7076 FStar_List.unzip in
            (match uu____7069 with
             | (pats,decls') ->
                 let uu____7177 = encode_formula body env2 in
                 (match uu____7177 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7196;
                             FStar_SMTEncoding_Term.rng = uu____7197;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7205 -> guards in
                      let uu____7208 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7208, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7242  ->
                   match uu____7242 with
                   | (x,uu____7246) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7252 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7258 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7258) uu____7252 tl1 in
             let uu____7260 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7272  ->
                       match uu____7272 with
                       | (b,uu____7276) ->
                           let uu____7277 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7277)) in
             (match uu____7260 with
              | None  -> ()
              | Some (x,uu____7281) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7291 =
                    let uu____7292 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7292 in
                  FStar_Errors.warn pos uu____7291) in
       let uu____7293 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7293 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7299 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7335  ->
                     match uu____7335 with
                     | (l,uu____7345) -> FStar_Ident.lid_equals op l)) in
           (match uu____7299 with
            | None  -> fallback phi1
            | Some (uu____7368,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7397 = encode_q_body env vars pats body in
             match uu____7397 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7423 =
                     let uu____7429 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7429) in
                   FStar_SMTEncoding_Term.mkForall uu____7423
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7441 = encode_q_body env vars pats body in
             match uu____7441 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7466 =
                   let uu____7467 =
                     let uu____7473 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7473) in
                   FStar_SMTEncoding_Term.mkExists uu____7467
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7466, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7522 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7522 with
  | (asym,a) ->
      let uu____7527 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7527 with
       | (xsym,x) ->
           let uu____7532 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7532 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7562 =
                      let uu____7568 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7568, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7562 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7583 =
                      let uu____7587 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7587) in
                    FStar_SMTEncoding_Util.mkApp uu____7583 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7595 =
                    let uu____7597 =
                      let uu____7599 =
                        let uu____7601 =
                          let uu____7602 =
                            let uu____7606 =
                              let uu____7607 =
                                let uu____7613 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7613) in
                              FStar_SMTEncoding_Util.mkForall uu____7607 in
                            (uu____7606, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Term.Assume uu____7602 in
                        let uu____7622 =
                          let uu____7624 =
                            let uu____7625 =
                              let uu____7629 =
                                let uu____7630 =
                                  let uu____7636 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7636) in
                                FStar_SMTEncoding_Util.mkForall uu____7630 in
                              (uu____7629,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Term.Assume uu____7625 in
                          [uu____7624] in
                        uu____7601 :: uu____7622 in
                      xtok_decl :: uu____7599 in
                    xname_decl :: uu____7597 in
                  (xtok1, uu____7595) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7685 =
                    let uu____7693 =
                      let uu____7699 =
                        let uu____7700 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7700 in
                      quant axy uu____7699 in
                    (FStar_Syntax_Const.op_Eq, uu____7693) in
                  let uu____7706 =
                    let uu____7715 =
                      let uu____7723 =
                        let uu____7729 =
                          let uu____7730 =
                            let uu____7731 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7731 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7730 in
                        quant axy uu____7729 in
                      (FStar_Syntax_Const.op_notEq, uu____7723) in
                    let uu____7737 =
                      let uu____7746 =
                        let uu____7754 =
                          let uu____7760 =
                            let uu____7761 =
                              let uu____7762 =
                                let uu____7765 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7766 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7765, uu____7766) in
                              FStar_SMTEncoding_Util.mkLT uu____7762 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7761 in
                          quant xy uu____7760 in
                        (FStar_Syntax_Const.op_LT, uu____7754) in
                      let uu____7772 =
                        let uu____7781 =
                          let uu____7789 =
                            let uu____7795 =
                              let uu____7796 =
                                let uu____7797 =
                                  let uu____7800 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7801 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7800, uu____7801) in
                                FStar_SMTEncoding_Util.mkLTE uu____7797 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7796 in
                            quant xy uu____7795 in
                          (FStar_Syntax_Const.op_LTE, uu____7789) in
                        let uu____7807 =
                          let uu____7816 =
                            let uu____7824 =
                              let uu____7830 =
                                let uu____7831 =
                                  let uu____7832 =
                                    let uu____7835 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7836 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7835, uu____7836) in
                                  FStar_SMTEncoding_Util.mkGT uu____7832 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7831 in
                              quant xy uu____7830 in
                            (FStar_Syntax_Const.op_GT, uu____7824) in
                          let uu____7842 =
                            let uu____7851 =
                              let uu____7859 =
                                let uu____7865 =
                                  let uu____7866 =
                                    let uu____7867 =
                                      let uu____7870 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7871 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7870, uu____7871) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7867 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7866 in
                                quant xy uu____7865 in
                              (FStar_Syntax_Const.op_GTE, uu____7859) in
                            let uu____7877 =
                              let uu____7886 =
                                let uu____7894 =
                                  let uu____7900 =
                                    let uu____7901 =
                                      let uu____7902 =
                                        let uu____7905 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7906 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7905, uu____7906) in
                                      FStar_SMTEncoding_Util.mkSub uu____7902 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7901 in
                                  quant xy uu____7900 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7894) in
                              let uu____7912 =
                                let uu____7921 =
                                  let uu____7929 =
                                    let uu____7935 =
                                      let uu____7936 =
                                        let uu____7937 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7937 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7936 in
                                    quant qx uu____7935 in
                                  (FStar_Syntax_Const.op_Minus, uu____7929) in
                                let uu____7943 =
                                  let uu____7952 =
                                    let uu____7960 =
                                      let uu____7966 =
                                        let uu____7967 =
                                          let uu____7968 =
                                            let uu____7971 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7972 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7971, uu____7972) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7968 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7967 in
                                      quant xy uu____7966 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7960) in
                                  let uu____7978 =
                                    let uu____7987 =
                                      let uu____7995 =
                                        let uu____8001 =
                                          let uu____8002 =
                                            let uu____8003 =
                                              let uu____8006 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8007 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8006, uu____8007) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8003 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8002 in
                                        quant xy uu____8001 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7995) in
                                    let uu____8013 =
                                      let uu____8022 =
                                        let uu____8030 =
                                          let uu____8036 =
                                            let uu____8037 =
                                              let uu____8038 =
                                                let uu____8041 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8042 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8041, uu____8042) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8038 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8037 in
                                          quant xy uu____8036 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8030) in
                                      let uu____8048 =
                                        let uu____8057 =
                                          let uu____8065 =
                                            let uu____8071 =
                                              let uu____8072 =
                                                let uu____8073 =
                                                  let uu____8076 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8077 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8076, uu____8077) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8073 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8072 in
                                            quant xy uu____8071 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8065) in
                                        let uu____8083 =
                                          let uu____8092 =
                                            let uu____8100 =
                                              let uu____8106 =
                                                let uu____8107 =
                                                  let uu____8108 =
                                                    let uu____8111 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8112 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8111, uu____8112) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8108 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8107 in
                                              quant xy uu____8106 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8100) in
                                          let uu____8118 =
                                            let uu____8127 =
                                              let uu____8135 =
                                                let uu____8141 =
                                                  let uu____8142 =
                                                    let uu____8143 =
                                                      let uu____8146 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8147 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8146,
                                                        uu____8147) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8143 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8142 in
                                                quant xy uu____8141 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8135) in
                                            let uu____8153 =
                                              let uu____8162 =
                                                let uu____8170 =
                                                  let uu____8176 =
                                                    let uu____8177 =
                                                      let uu____8178 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8178 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8177 in
                                                  quant qx uu____8176 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8170) in
                                              [uu____8162] in
                                            uu____8127 :: uu____8153 in
                                          uu____8092 :: uu____8118 in
                                        uu____8057 :: uu____8083 in
                                      uu____8022 :: uu____8048 in
                                    uu____7987 :: uu____8013 in
                                  uu____7952 :: uu____7978 in
                                uu____7921 :: uu____7943 in
                              uu____7886 :: uu____7912 in
                            uu____7851 :: uu____7877 in
                          uu____7816 :: uu____7842 in
                        uu____7781 :: uu____7807 in
                      uu____7746 :: uu____7772 in
                    uu____7715 :: uu____7737 in
                  uu____7685 :: uu____7706 in
                let mk1 l v1 =
                  let uu____8306 =
                    let uu____8311 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8343  ->
                              match uu____8343 with
                              | (l',uu____8352) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8311
                      (FStar_Option.map
                         (fun uu____8385  ->
                            match uu____8385 with | (uu____8396,b) -> b v1)) in
                  FStar_All.pipe_right uu____8306 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8437  ->
                          match uu____8437 with
                          | (l',uu____8446) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8472 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8472 with
        | (xxsym,xx) ->
            let uu____8477 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8477 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8485 =
                   let uu____8489 =
                     let uu____8490 =
                       let uu____8496 =
                         let uu____8497 =
                           let uu____8500 =
                             let uu____8501 =
                               let uu____8504 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8504) in
                             FStar_SMTEncoding_Util.mkEq uu____8501 in
                           (xx_has_type, uu____8500) in
                         FStar_SMTEncoding_Util.mkImp uu____8497 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8496) in
                     FStar_SMTEncoding_Util.mkForall uu____8490 in
                   let uu____8517 =
                     let uu____8518 =
                       let uu____8519 =
                         let uu____8520 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8520 in
                       Prims.strcat module_name uu____8519 in
                     varops.mk_unique uu____8518 in
                   (uu____8489, (Some "pretyping"), uu____8517) in
                 FStar_SMTEncoding_Term.Assume uu____8485)
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
    let uu____8550 =
      let uu____8551 =
        let uu____8555 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8555, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Term.Assume uu____8551 in
    let uu____8557 =
      let uu____8559 =
        let uu____8560 =
          let uu____8564 =
            let uu____8565 =
              let uu____8571 =
                let uu____8572 =
                  let uu____8575 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8575) in
                FStar_SMTEncoding_Util.mkImp uu____8572 in
              ([[typing_pred]], [xx], uu____8571) in
            mkForall_fuel uu____8565 in
          (uu____8564, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8560 in
      [uu____8559] in
    uu____8550 :: uu____8557 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8603 =
      let uu____8604 =
        let uu____8608 =
          let uu____8609 =
            let uu____8615 =
              let uu____8618 =
                let uu____8620 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8620] in
              [uu____8618] in
            let uu____8623 =
              let uu____8624 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8624 tt in
            (uu____8615, [bb], uu____8623) in
          FStar_SMTEncoding_Util.mkForall uu____8609 in
        (uu____8608, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Term.Assume uu____8604 in
    let uu____8635 =
      let uu____8637 =
        let uu____8638 =
          let uu____8642 =
            let uu____8643 =
              let uu____8649 =
                let uu____8650 =
                  let uu____8653 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8653) in
                FStar_SMTEncoding_Util.mkImp uu____8650 in
              ([[typing_pred]], [xx], uu____8649) in
            mkForall_fuel uu____8643 in
          (uu____8642, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8638 in
      [uu____8637] in
    uu____8603 :: uu____8635 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8687 =
        let uu____8688 =
          let uu____8692 =
            let uu____8694 =
              let uu____8696 =
                let uu____8698 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8699 =
                  let uu____8701 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8701] in
                uu____8698 :: uu____8699 in
              tt :: uu____8696 in
            tt :: uu____8694 in
          ("Prims.Precedes", uu____8692) in
        FStar_SMTEncoding_Util.mkApp uu____8688 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8687 in
    let precedes_y_x =
      let uu____8704 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8704 in
    let uu____8706 =
      let uu____8707 =
        let uu____8711 =
          let uu____8712 =
            let uu____8718 =
              let uu____8721 =
                let uu____8723 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8723] in
              [uu____8721] in
            let uu____8726 =
              let uu____8727 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8727 tt in
            (uu____8718, [bb], uu____8726) in
          FStar_SMTEncoding_Util.mkForall uu____8712 in
        (uu____8711, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Term.Assume uu____8707 in
    let uu____8738 =
      let uu____8740 =
        let uu____8741 =
          let uu____8745 =
            let uu____8746 =
              let uu____8752 =
                let uu____8753 =
                  let uu____8756 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8756) in
                FStar_SMTEncoding_Util.mkImp uu____8753 in
              ([[typing_pred]], [xx], uu____8752) in
            mkForall_fuel uu____8746 in
          (uu____8745, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8741 in
      let uu____8769 =
        let uu____8771 =
          let uu____8772 =
            let uu____8776 =
              let uu____8777 =
                let uu____8783 =
                  let uu____8784 =
                    let uu____8787 =
                      let uu____8788 =
                        let uu____8790 =
                          let uu____8792 =
                            let uu____8794 =
                              let uu____8795 =
                                let uu____8798 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8799 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8798, uu____8799) in
                              FStar_SMTEncoding_Util.mkGT uu____8795 in
                            let uu____8800 =
                              let uu____8802 =
                                let uu____8803 =
                                  let uu____8806 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8807 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8806, uu____8807) in
                                FStar_SMTEncoding_Util.mkGTE uu____8803 in
                              let uu____8808 =
                                let uu____8810 =
                                  let uu____8811 =
                                    let uu____8814 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8815 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8814, uu____8815) in
                                  FStar_SMTEncoding_Util.mkLT uu____8811 in
                                [uu____8810] in
                              uu____8802 :: uu____8808 in
                            uu____8794 :: uu____8800 in
                          typing_pred_y :: uu____8792 in
                        typing_pred :: uu____8790 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8788 in
                    (uu____8787, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8784 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8783) in
              mkForall_fuel uu____8777 in
            (uu____8776, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Term.Assume uu____8772 in
        [uu____8771] in
      uu____8740 :: uu____8769 in
    uu____8706 :: uu____8738 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8845 =
      let uu____8846 =
        let uu____8850 =
          let uu____8851 =
            let uu____8857 =
              let uu____8860 =
                let uu____8862 = FStar_SMTEncoding_Term.boxString b in
                [uu____8862] in
              [uu____8860] in
            let uu____8865 =
              let uu____8866 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8866 tt in
            (uu____8857, [bb], uu____8865) in
          FStar_SMTEncoding_Util.mkForall uu____8851 in
        (uu____8850, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Term.Assume uu____8846 in
    let uu____8877 =
      let uu____8879 =
        let uu____8880 =
          let uu____8884 =
            let uu____8885 =
              let uu____8891 =
                let uu____8892 =
                  let uu____8895 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8895) in
                FStar_SMTEncoding_Util.mkImp uu____8892 in
              ([[typing_pred]], [xx], uu____8891) in
            mkForall_fuel uu____8885 in
          (uu____8884, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8880 in
      [uu____8879] in
    uu____8845 :: uu____8877 in
  let mk_ref1 env reft_name uu____8917 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8928 =
        let uu____8932 =
          let uu____8934 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8934] in
        (reft_name, uu____8932) in
      FStar_SMTEncoding_Util.mkApp uu____8928 in
    let refb =
      let uu____8937 =
        let uu____8941 =
          let uu____8943 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8943] in
        (reft_name, uu____8941) in
      FStar_SMTEncoding_Util.mkApp uu____8937 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8947 =
      let uu____8948 =
        let uu____8952 =
          let uu____8953 =
            let uu____8959 =
              let uu____8960 =
                let uu____8963 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8963) in
              FStar_SMTEncoding_Util.mkImp uu____8960 in
            ([[typing_pred]], [xx; aa], uu____8959) in
          mkForall_fuel uu____8953 in
        (uu____8952, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Term.Assume uu____8948 in
    let uu____8978 =
      let uu____8980 =
        let uu____8981 =
          let uu____8985 =
            let uu____8986 =
              let uu____8992 =
                let uu____8993 =
                  let uu____8996 =
                    FStar_SMTEncoding_Util.mkAnd (typing_pred, typing_pred_b) in
                  let uu____8997 =
                    let uu____8998 =
                      let uu____9001 = FStar_SMTEncoding_Util.mkFreeV aa in
                      let uu____9002 = FStar_SMTEncoding_Util.mkFreeV bb in
                      (uu____9001, uu____9002) in
                    FStar_SMTEncoding_Util.mkEq uu____8998 in
                  (uu____8996, uu____8997) in
                FStar_SMTEncoding_Util.mkImp uu____8993 in
              ([[typing_pred; typing_pred_b]], [xx; aa; bb], uu____8992) in
            mkForall_fuel' (Prims.parse_int "2") uu____8986 in
          (uu____8985, (Some "ref typing is injective"), "ref_injectivity") in
        FStar_SMTEncoding_Term.Assume uu____8981 in
      [uu____8980] in
    uu____8947 :: uu____8978 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9044 =
      let uu____9045 =
        let uu____9049 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9049, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Term.Assume uu____9045 in
    [uu____9044] in
  let mk_and_interp env conj uu____9060 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9070 =
        let uu____9074 =
          let uu____9076 = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
          [uu____9076] in
        ("Valid", uu____9074) in
      FStar_SMTEncoding_Util.mkApp uu____9070 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9083 =
      let uu____9084 =
        let uu____9088 =
          let uu____9089 =
            let uu____9095 =
              let uu____9096 =
                let uu____9099 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9099, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9096 in
            ([[valid]], [aa; bb], uu____9095) in
          FStar_SMTEncoding_Util.mkForall uu____9089 in
        (uu____9088, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Term.Assume uu____9084 in
    [uu____9083] in
  let mk_or_interp env disj uu____9123 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9133 =
        let uu____9137 =
          let uu____9139 = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
          [uu____9139] in
        ("Valid", uu____9137) in
      FStar_SMTEncoding_Util.mkApp uu____9133 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9146 =
      let uu____9147 =
        let uu____9151 =
          let uu____9152 =
            let uu____9158 =
              let uu____9159 =
                let uu____9162 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9162, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9159 in
            ([[valid]], [aa; bb], uu____9158) in
          FStar_SMTEncoding_Util.mkForall uu____9152 in
        (uu____9151, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Term.Assume uu____9147 in
    [uu____9146] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let valid =
      let uu____9200 =
        let uu____9204 =
          let uu____9206 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
          [uu____9206] in
        ("Valid", uu____9204) in
      FStar_SMTEncoding_Util.mkApp uu____9200 in
    let uu____9209 =
      let uu____9210 =
        let uu____9214 =
          let uu____9215 =
            let uu____9221 =
              let uu____9222 =
                let uu____9225 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9225, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9222 in
            ([[valid]], [aa; xx1; yy1], uu____9221) in
          FStar_SMTEncoding_Util.mkForall uu____9215 in
        (uu____9214, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Term.Assume uu____9210 in
    [uu____9209] in
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
      let uu____9269 =
        let uu____9273 =
          let uu____9275 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
          [uu____9275] in
        ("Valid", uu____9273) in
      FStar_SMTEncoding_Util.mkApp uu____9269 in
    let uu____9278 =
      let uu____9279 =
        let uu____9283 =
          let uu____9284 =
            let uu____9290 =
              let uu____9291 =
                let uu____9294 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9294, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9291 in
            ([[valid]], [aa; bb; xx1; yy1], uu____9290) in
          FStar_SMTEncoding_Util.mkForall uu____9284 in
        (uu____9283, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Term.Assume uu____9279 in
    [uu____9278] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9332 =
        let uu____9336 =
          let uu____9338 = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
          [uu____9338] in
        ("Valid", uu____9336) in
      FStar_SMTEncoding_Util.mkApp uu____9332 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9345 =
      let uu____9346 =
        let uu____9350 =
          let uu____9351 =
            let uu____9357 =
              let uu____9358 =
                let uu____9361 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9361, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9358 in
            ([[valid]], [aa; bb], uu____9357) in
          FStar_SMTEncoding_Util.mkForall uu____9351 in
        (uu____9350, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Term.Assume uu____9346 in
    [uu____9345] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9395 =
        let uu____9399 =
          let uu____9401 = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
          [uu____9401] in
        ("Valid", uu____9399) in
      FStar_SMTEncoding_Util.mkApp uu____9395 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9408 =
      let uu____9409 =
        let uu____9413 =
          let uu____9414 =
            let uu____9420 =
              let uu____9421 =
                let uu____9424 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9424, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9421 in
            ([[valid]], [aa; bb], uu____9420) in
          FStar_SMTEncoding_Util.mkForall uu____9414 in
        (uu____9413, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Term.Assume uu____9409 in
    [uu____9408] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let valid =
      let uu____9454 =
        let uu____9458 =
          let uu____9460 = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
          [uu____9460] in
        ("Valid", uu____9458) in
      FStar_SMTEncoding_Util.mkApp uu____9454 in
    let not_valid_a =
      let uu____9464 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9464 in
    let uu____9466 =
      let uu____9467 =
        let uu____9471 =
          let uu____9472 =
            let uu____9478 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[valid]], [aa], uu____9478) in
          FStar_SMTEncoding_Util.mkForall uu____9472 in
        (uu____9471, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Term.Assume uu____9467 in
    [uu____9466] in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let valid =
      let uu____9514 =
        let uu____9518 =
          let uu____9520 = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b]) in
          [uu____9520] in
        ("Valid", uu____9518) in
      FStar_SMTEncoding_Util.mkApp uu____9514 in
    let valid_b_x =
      let uu____9524 =
        let uu____9528 =
          let uu____9530 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9530] in
        ("Valid", uu____9528) in
      FStar_SMTEncoding_Util.mkApp uu____9524 in
    let uu____9532 =
      let uu____9533 =
        let uu____9537 =
          let uu____9538 =
            let uu____9544 =
              let uu____9545 =
                let uu____9548 =
                  let uu____9549 =
                    let uu____9555 =
                      let uu____9558 =
                        let uu____9560 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9560] in
                      [uu____9558] in
                    let uu____9563 =
                      let uu____9564 =
                        let uu____9567 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9567, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9564 in
                    (uu____9555, [xx1], uu____9563) in
                  FStar_SMTEncoding_Util.mkForall uu____9549 in
                (uu____9548, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9545 in
            ([[valid]], [aa; bb], uu____9544) in
          FStar_SMTEncoding_Util.mkForall uu____9538 in
        (uu____9537, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Term.Assume uu____9533 in
    [uu____9532] in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let valid =
      let uu____9614 =
        let uu____9618 =
          let uu____9620 = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b]) in
          [uu____9620] in
        ("Valid", uu____9618) in
      FStar_SMTEncoding_Util.mkApp uu____9614 in
    let valid_b_x =
      let uu____9624 =
        let uu____9628 =
          let uu____9630 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9630] in
        ("Valid", uu____9628) in
      FStar_SMTEncoding_Util.mkApp uu____9624 in
    let uu____9632 =
      let uu____9633 =
        let uu____9637 =
          let uu____9638 =
            let uu____9644 =
              let uu____9645 =
                let uu____9648 =
                  let uu____9649 =
                    let uu____9655 =
                      let uu____9658 =
                        let uu____9660 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9660] in
                      [uu____9658] in
                    let uu____9663 =
                      let uu____9664 =
                        let uu____9667 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9667, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9664 in
                    (uu____9655, [xx1], uu____9663) in
                  FStar_SMTEncoding_Util.mkExists uu____9649 in
                (uu____9648, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9645 in
            ([[valid]], [aa; bb], uu____9644) in
          FStar_SMTEncoding_Util.mkForall uu____9638 in
        (uu____9637, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Term.Assume uu____9633 in
    [uu____9632] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9703 =
      let uu____9704 =
        let uu____9708 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9709 = varops.mk_unique "typing_range_const" in
        (uu____9708, (Some "Range_const typing"), uu____9709) in
      FStar_SMTEncoding_Term.Assume uu____9704 in
    [uu____9703] in
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
          let uu____9971 =
            FStar_Util.find_opt
              (fun uu____9989  ->
                 match uu____9989 with
                 | (l,uu____9999) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9971 with
          | None  -> []
          | Some (uu____10021,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10058 = encode_function_type_as_formula None None t env in
        match uu____10058 with
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
            let uu____10090 =
              (let uu____10091 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10091) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10090
            then
              let uu____10095 = new_term_constant_and_tok_from_lid env lid in
              match uu____10095 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10107 =
                      let uu____10108 = FStar_Syntax_Subst.compress t_norm in
                      uu____10108.FStar_Syntax_Syntax.n in
                    match uu____10107 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10113) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10130  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10133 -> [] in
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
              (let uu____10142 = prims.is lid in
               if uu____10142
               then
                 let vname = varops.new_fvar lid in
                 let uu____10147 = prims.mk lid vname in
                 match uu____10147 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10162 =
                    let uu____10168 = curried_arrow_formals_comp t_norm in
                    match uu____10168 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10179 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10179
                          then
                            let uu____10180 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___153_10181 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___153_10181.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___153_10181.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___153_10181.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___153_10181.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___153_10181.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___153_10181.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___153_10181.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___153_10181.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___153_10181.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___153_10181.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___153_10181.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___153_10181.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___153_10181.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___153_10181.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___153_10181.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___153_10181.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___153_10181.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___153_10181.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___153_10181.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___153_10181.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___153_10181.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___153_10181.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___153_10181.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10180
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10188 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10188)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10162 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10215 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10215 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10228 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___124_10252  ->
                                     match uu___124_10252 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10255 =
                                           FStar_Util.prefix vars in
                                         (match uu____10255 with
                                          | (uu____10266,(xxsym,uu____10268))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10278 =
                                                let uu____10279 =
                                                  let uu____10283 =
                                                    let uu____10284 =
                                                      let uu____10290 =
                                                        let uu____10291 =
                                                          let uu____10294 =
                                                            let uu____10295 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10295 in
                                                          (vapp, uu____10294) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10291 in
                                                      ([[vapp]], vars,
                                                        uu____10290) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10284 in
                                                  (uu____10283,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10279 in
                                              [uu____10278])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10306 =
                                           FStar_Util.prefix vars in
                                         (match uu____10306 with
                                          | (uu____10317,(xxsym,uu____10319))
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
                                              let uu____10333 =
                                                let uu____10334 =
                                                  let uu____10338 =
                                                    let uu____10339 =
                                                      let uu____10345 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10345) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10339 in
                                                  (uu____10338,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10334 in
                                              [uu____10333])
                                     | uu____10354 -> [])) in
                           let uu____10355 = encode_binders None formals env1 in
                           (match uu____10355 with
                            | (vars,guards,env',decls1,uu____10371) ->
                                let uu____10378 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10383 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10383, decls1)
                                  | Some p ->
                                      let uu____10385 = encode_formula p env' in
                                      (match uu____10385 with
                                       | (g,ds) ->
                                           let uu____10392 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10392,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10378 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10401 =
                                         let uu____10405 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10405) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10401 in
                                     let uu____10410 =
                                       let vname_decl =
                                         let uu____10415 =
                                           let uu____10421 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10426  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10421,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10415 in
                                       let uu____10431 =
                                         let env2 =
                                           let uu___154_10435 = env1 in
                                           {
                                             bindings =
                                               (uu___154_10435.bindings);
                                             depth = (uu___154_10435.depth);
                                             tcenv = (uu___154_10435.tcenv);
                                             warn = (uu___154_10435.warn);
                                             cache = (uu___154_10435.cache);
                                             nolabels =
                                               (uu___154_10435.nolabels);
                                             use_zfuel_name =
                                               (uu___154_10435.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___154_10435.current_module_name)
                                           } in
                                         let uu____10436 =
                                           let uu____10437 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10437 in
                                         if uu____10436
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10431 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10447::uu____10448 ->
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
                                                   let uu____10471 =
                                                     let uu____10477 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10477) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10471 in
                                                 FStar_SMTEncoding_Term.Assume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10491 ->
                                                 FStar_SMTEncoding_Term.Assume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10493 =
                                             match formals with
                                             | [] ->
                                                 let uu____10502 =
                                                   let uu____10503 =
                                                     let uu____10505 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10505 in
                                                   push_free_var env1 lid
                                                     vname uu____10503 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10502)
                                             | uu____10508 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10513 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10513 in
                                                 let name_tok_corr =
                                                   let uu____10515 =
                                                     let uu____10519 =
                                                       let uu____10520 =
                                                         let uu____10526 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10526) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10520 in
                                                     (uu____10519,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Term.Assume
                                                     uu____10515 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10493 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10410 with
                                      | (decls2,env2) ->
                                          let uu____10550 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10555 =
                                              encode_term res_t1 env' in
                                            match uu____10555 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10563 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10563,
                                                  decls) in
                                          (match uu____10550 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10571 =
                                                   let uu____10575 =
                                                     let uu____10576 =
                                                       let uu____10582 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10582) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10576 in
                                                   (uu____10575,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____10571 in
                                               let freshness =
                                                 let uu____10591 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10591
                                                 then
                                                   let uu____10594 =
                                                     let uu____10595 =
                                                       let uu____10601 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10607 =
                                                         varops.next_id () in
                                                       (vname, uu____10601,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10607) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10595 in
                                                   let uu____10609 =
                                                     let uu____10611 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10611] in
                                                   uu____10594 :: uu____10609
                                                 else [] in
                                               let g =
                                                 let uu____10615 =
                                                   let uu____10617 =
                                                     let uu____10619 =
                                                       let uu____10621 =
                                                         let uu____10623 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10623 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10621 in
                                                     FStar_List.append decls3
                                                       uu____10619 in
                                                   FStar_List.append decls2
                                                     uu____10617 in
                                                 FStar_List.append decls11
                                                   uu____10615 in
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
          let uu____10645 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10645 with
          | None  ->
              let uu____10668 = encode_free_var env x t t_norm [] in
              (match uu____10668 with
               | (decls,env1) ->
                   let uu____10683 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10683 with
                    | (n1,x',uu____10702) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10714) -> ((n1, x1), [], env)
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
          let uu____10747 = encode_free_var env lid t tt quals in
          match uu____10747 with
          | (decls,env1) ->
              let uu____10758 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10758
              then
                let uu____10762 =
                  let uu____10764 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10764 in
                (uu____10762, env1)
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
             (fun uu____10792  ->
                fun lb  ->
                  match uu____10792 with
                  | (decls,env1) ->
                      let uu____10804 =
                        let uu____10808 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10808
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10804 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10822 = FStar_Syntax_Util.head_and_args t in
    match uu____10822 with
    | (hd1,args) ->
        let uu____10848 =
          let uu____10849 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10849.FStar_Syntax_Syntax.n in
        (match uu____10848 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10853,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10866 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10881  ->
      fun quals  ->
        match uu____10881 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10930 = FStar_Util.first_N nbinders formals in
              match uu____10930 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10970  ->
                         fun uu____10971  ->
                           match (uu____10970, uu____10971) with
                           | ((formal,uu____10981),(binder,uu____10983)) ->
                               let uu____10988 =
                                 let uu____10993 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10993) in
                               FStar_Syntax_Syntax.NT uu____10988) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10998 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11012  ->
                              match uu____11012 with
                              | (x,i) ->
                                  let uu____11019 =
                                    let uu___155_11020 = x in
                                    let uu____11021 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___155_11020.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___155_11020.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11021
                                    } in
                                  (uu____11019, i))) in
                    FStar_All.pipe_right uu____10998
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11033 =
                      let uu____11035 =
                        let uu____11036 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11036.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____11035 in
                    let uu____11040 =
                      let uu____11041 = FStar_Syntax_Subst.compress body in
                      let uu____11042 =
                        let uu____11043 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____11043 in
                      FStar_Syntax_Syntax.extend_app_n uu____11041
                        uu____11042 in
                    uu____11040 uu____11033 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11085 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11085
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___156_11086 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___156_11086.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___156_11086.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___156_11086.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___156_11086.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___156_11086.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___156_11086.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___156_11086.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___156_11086.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___156_11086.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___156_11086.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___156_11086.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___156_11086.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___156_11086.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___156_11086.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___156_11086.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___156_11086.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___156_11086.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___156_11086.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___156_11086.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___156_11086.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___156_11086.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___156_11086.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___156_11086.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11107 = FStar_Syntax_Util.abs_formals e in
                match uu____11107 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11156::uu____11157 ->
                         let uu____11165 =
                           let uu____11166 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11166.FStar_Syntax_Syntax.n in
                         (match uu____11165 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11193 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11193 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11219 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11219
                                   then
                                     let uu____11237 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11237 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11283  ->
                                                   fun uu____11284  ->
                                                     match (uu____11283,
                                                             uu____11284)
                                                     with
                                                     | ((x,uu____11294),
                                                        (b,uu____11296)) ->
                                                         let uu____11301 =
                                                           let uu____11306 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11306) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11301)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11308 =
                                            let uu____11319 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11319) in
                                          (uu____11308, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11354 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11354 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11406) ->
                              let uu____11411 =
                                let uu____11422 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11422 in
                              (uu____11411, true)
                          | uu____11455 when Prims.op_Negation norm1 ->
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
                          | uu____11457 ->
                              let uu____11458 =
                                let uu____11459 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11460 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11459
                                  uu____11460 in
                              failwith uu____11458)
                     | uu____11473 ->
                         let uu____11474 =
                           let uu____11475 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11475.FStar_Syntax_Syntax.n in
                         (match uu____11474 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11502 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11502 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11520 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11520 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11568 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11596 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11596
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11603 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11644  ->
                            fun lb  ->
                              match uu____11644 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11695 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11695
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11698 =
                                      let uu____11706 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11706
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11698 with
                                    | (tok,decl,env2) ->
                                        let uu____11731 =
                                          let uu____11738 =
                                            let uu____11744 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11744, tok) in
                                          uu____11738 :: toks in
                                        (uu____11731, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11603 with
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
                        | uu____11846 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11851 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11851 vars)
                            else
                              (let uu____11853 =
                                 let uu____11857 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11857) in
                               FStar_SMTEncoding_Util.mkApp uu____11853) in
                      let uu____11862 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___125_11864  ->
                                 match uu___125_11864 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11865 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11868 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11868))) in
                      if uu____11862
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11888;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11890;
                                FStar_Syntax_Syntax.lbeff = uu____11891;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11932 =
                                 FStar_Syntax_Subst.univ_var_opening uvs in
                               (match uu____11932 with
                                | (univ_subst,univ_vars1) ->
                                    let env' =
                                      let uu___159_11947 = env1 in
                                      let uu____11948 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1.tcenv univ_vars1 in
                                      {
                                        bindings = (uu___159_11947.bindings);
                                        depth = (uu___159_11947.depth);
                                        tcenv = uu____11948;
                                        warn = (uu___159_11947.warn);
                                        cache = (uu___159_11947.cache);
                                        nolabels = (uu___159_11947.nolabels);
                                        use_zfuel_name =
                                          (uu___159_11947.use_zfuel_name);
                                        encode_non_total_function_typ =
                                          (uu___159_11947.encode_non_total_function_typ);
                                        current_module_name =
                                          (uu___159_11947.current_module_name)
                                      } in
                                    let t_norm1 =
                                      FStar_Syntax_Subst.subst univ_subst
                                        t_norm in
                                    let e1 =
                                      let uu____11951 =
                                        FStar_Syntax_Subst.subst univ_subst e in
                                      FStar_Syntax_Subst.compress uu____11951 in
                                    let uu____11952 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11952 with
                                     | ((binders,body,uu____11964,uu____11965),curry)
                                         ->
                                         ((let uu____11972 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11972
                                           then
                                             let uu____11973 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11974 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11973 uu____11974
                                           else ());
                                          (let uu____11976 =
                                             encode_binders None binders env' in
                                           match uu____11976 with
                                           | (vars,guards,env'1,binder_decls,uu____11992)
                                               ->
                                               let body1 =
                                                 let uu____12000 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12000
                                                 then
                                                   reify_body env'1.tcenv
                                                     body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12003 =
                                                 let uu____12008 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12008
                                                 then
                                                   let uu____12014 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12015 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12014, uu____12015)
                                                 else
                                                   (let uu____12021 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12021)) in
                                               (match uu____12003 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12035 =
                                                        let uu____12039 =
                                                          let uu____12040 =
                                                            let uu____12046 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12046) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12040 in
                                                        let uu____12052 =
                                                          let uu____12054 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12054 in
                                                        (uu____12039,
                                                          uu____12052,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Term.Assume
                                                        uu____12035 in
                                                    let uu____12056 =
                                                      let uu____12058 =
                                                        let uu____12060 =
                                                          let uu____12062 =
                                                            let uu____12064 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12064 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12062 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12060 in
                                                      FStar_List.append
                                                        decls1 uu____12058 in
                                                    (uu____12056, env1))))))
                           | uu____12067 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12086 = varops.fresh "fuel" in
                             (uu____12086, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12089 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12128  ->
                                     fun uu____12129  ->
                                       match (uu____12128, uu____12129) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12211 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12211 in
                                           let gtok =
                                             let uu____12213 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12213 in
                                           let env3 =
                                             let uu____12215 =
                                               let uu____12217 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12217 in
                                             push_free_var env2 flid gtok
                                               uu____12215 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12089 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12301
                                 t_norm uu____12303 =
                                 match (uu____12301, uu____12303) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12328;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12329;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12346 =
                                       FStar_Syntax_Subst.univ_var_opening
                                         uvs in
                                     (match uu____12346 with
                                      | (univ_subst,univ_vars1) ->
                                          let env' =
                                            let uu___160_12363 = env2 in
                                            let uu____12364 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env2.tcenv univ_vars1 in
                                            {
                                              bindings =
                                                (uu___160_12363.bindings);
                                              depth = (uu___160_12363.depth);
                                              tcenv = uu____12364;
                                              warn = (uu___160_12363.warn);
                                              cache = (uu___160_12363.cache);
                                              nolabels =
                                                (uu___160_12363.nolabels);
                                              use_zfuel_name =
                                                (uu___160_12363.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___160_12363.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___160_12363.current_module_name)
                                            } in
                                          let t_norm1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst t_norm in
                                          let e1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst e in
                                          ((let uu____12368 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12368
                                            then
                                              let uu____12369 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12370 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12371 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12369 uu____12370
                                                uu____12371
                                            else ());
                                           (let uu____12373 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12373 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12395 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12395
                                                  then
                                                    let uu____12396 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12397 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12398 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12399 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12396 uu____12397
                                                      uu____12398 uu____12399
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12403 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12403 with
                                                  | (vars,guards,env'1,binder_decls,uu____12421)
                                                      ->
                                                      let decl_g =
                                                        let uu____12429 =
                                                          let uu____12435 =
                                                            let uu____12437 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12437 in
                                                          (g, uu____12435,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12429 in
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
                                                        let uu____12452 =
                                                          let uu____12456 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12456) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12452 in
                                                      let gsapp =
                                                        let uu____12462 =
                                                          let uu____12466 =
                                                            let uu____12468 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12468 ::
                                                              vars_tm in
                                                          (g, uu____12466) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12462 in
                                                      let gmax =
                                                        let uu____12472 =
                                                          let uu____12476 =
                                                            let uu____12478 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12478 ::
                                                              vars_tm in
                                                          (g, uu____12476) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12472 in
                                                      let body1 =
                                                        let uu____12482 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12482
                                                        then
                                                          reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12484 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12484 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12495
                                                               =
                                                               let uu____12499
                                                                 =
                                                                 let uu____12500
                                                                   =
                                                                   let uu____12508
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
                                                                    uu____12508) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12500 in
                                                               let uu____12519
                                                                 =
                                                                 let uu____12521
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12521 in
                                                               (uu____12499,
                                                                 uu____12519,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12495 in
                                                           let eqn_f =
                                                             let uu____12524
                                                               =
                                                               let uu____12528
                                                                 =
                                                                 let uu____12529
                                                                   =
                                                                   let uu____12535
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12535) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12529 in
                                                               (uu____12528,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12524 in
                                                           let eqn_g' =
                                                             let uu____12543
                                                               =
                                                               let uu____12547
                                                                 =
                                                                 let uu____12548
                                                                   =
                                                                   let uu____12554
                                                                    =
                                                                    let uu____12555
                                                                    =
                                                                    let uu____12558
                                                                    =
                                                                    let uu____12559
                                                                    =
                                                                    let uu____12563
                                                                    =
                                                                    let uu____12565
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12565
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12563) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12559 in
                                                                    (gsapp,
                                                                    uu____12558) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12555 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12554) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12548 in
                                                               (uu____12547,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12543 in
                                                           let uu____12577 =
                                                             let uu____12582
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12582
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12599)
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
                                                                    let uu____12614
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12614
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12617
                                                                    =
                                                                    let uu____12621
                                                                    =
                                                                    let uu____12622
                                                                    =
                                                                    let uu____12628
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12628) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12622 in
                                                                    (uu____12621,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Term.Assume
                                                                    uu____12617 in
                                                                 let uu____12639
                                                                   =
                                                                   let uu____12643
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12643
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12651
                                                                    =
                                                                    let uu____12653
                                                                    =
                                                                    let uu____12654
                                                                    =
                                                                    let uu____12658
                                                                    =
                                                                    let uu____12659
                                                                    =
                                                                    let uu____12665
                                                                    =
                                                                    let uu____12666
                                                                    =
                                                                    let uu____12669
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12669,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12666 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12665) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12659 in
                                                                    (uu____12658,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12654 in
                                                                    [uu____12653] in
                                                                    (d3,
                                                                    uu____12651) in
                                                                 (match uu____12639
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12577
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
                               let uu____12704 =
                                 let uu____12711 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12743  ->
                                      fun uu____12744  ->
                                        match (uu____12743, uu____12744) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12820 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12820 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12711 in
                               (match uu____12704 with
                                | (decls2,eqns,env01) ->
                                    let uu____12860 =
                                      let isDeclFun uu___126_12868 =
                                        match uu___126_12868 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12869 -> true
                                        | uu____12875 -> false in
                                      let uu____12876 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12876
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12860 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12903 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12903
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
      (let uu____12936 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____12936
       then
         let uu____12937 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
           uu____12937
       else ());
      (let nm =
         let uu____12940 = FStar_Syntax_Util.lid_of_sigelt se in
         match uu____12940 with | None  -> "" | Some l -> l.FStar_Ident.str in
       let uu____12943 = encode_sigelt' env se in
       match uu____12943 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12952 =
                  let uu____12954 =
                    let uu____12955 = FStar_Util.format1 "<Skipped %s/>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12955 in
                  [uu____12954] in
                (uu____12952, e)
            | uu____12957 ->
                let uu____12958 =
                  let uu____12960 =
                    let uu____12962 =
                      let uu____12963 =
                        FStar_Util.format1 "<Start encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12963 in
                    uu____12962 :: g in
                  let uu____12964 =
                    let uu____12966 =
                      let uu____12967 =
                        FStar_Util.format1 "</end encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12967 in
                    [uu____12966] in
                  FStar_List.append uu____12960 uu____12964 in
                (uu____12958, e)))
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12975 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12984 =
            let uu____12985 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12985 Prims.op_Negation in
          if uu____12984
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13005 ->
                   let uu____13006 =
                     let uu____13009 =
                       let uu____13010 =
                         let uu____13025 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13025) in
                       FStar_Syntax_Syntax.Tm_abs uu____13010 in
                     FStar_Syntax_Syntax.mk uu____13009 in
                   uu____13006 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13078 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13078 with
               | (aname,atok,env2) ->
                   let uu____13088 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13088 with
                    | (formals,uu____13098) ->
                        let uu____13105 =
                          let uu____13108 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13108 env2 in
                        (match uu____13105 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13116 =
                                 let uu____13117 =
                                   let uu____13123 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13131  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13123,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13117 in
                               [uu____13116;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13138 =
                               let aux uu____13167 uu____13168 =
                                 match (uu____13167, uu____13168) with
                                 | ((bv,uu____13195),(env3,acc_sorts,acc)) ->
                                     let uu____13216 = gen_term_var env3 bv in
                                     (match uu____13216 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13138 with
                              | (uu____13254,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13268 =
                                      let uu____13272 =
                                        let uu____13273 =
                                          let uu____13279 =
                                            let uu____13280 =
                                              let uu____13283 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13283) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13280 in
                                          ([[app]], xs_sorts, uu____13279) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13273 in
                                      (uu____13272, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Term.Assume uu____13268 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13295 =
                                      let uu____13299 =
                                        let uu____13300 =
                                          let uu____13306 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13306) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13300 in
                                      (uu____13299,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Term.Assume uu____13295 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13316 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13316 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____13332,uu____13333,uu____13334) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13337 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13337 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13348,t,quals) ->
          let will_encode_definition =
            let uu____13354 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___127_13356  ->
                      match uu___127_13356 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13359 -> false)) in
            Prims.op_Negation uu____13354 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13365 = encode_top_level_val env fv t quals in
             match uu____13365 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13377 =
                   let uu____13379 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13379 in
                 (uu____13377, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____13384) ->
          let uu____13387 = encode_formula f env in
          (match uu____13387 with
           | (f1,decls) ->
               let g =
                 let uu____13396 =
                   let uu____13397 =
                     let uu____13401 =
                       let uu____13403 =
                         let uu____13404 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13404 in
                       Some uu____13403 in
                     let uu____13405 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13401, uu____13405) in
                   FStar_SMTEncoding_Term.Assume uu____13397 in
                 [uu____13396] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13409,quals,uu____13411) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13419 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13426 =
                       let uu____13431 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13431.FStar_Syntax_Syntax.fv_name in
                     uu____13426.FStar_Syntax_Syntax.v in
                   let uu____13435 =
                     let uu____13436 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13436 in
                   if uu____13435
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
                     let uu____13455 = encode_sigelt' env1 val_decl in
                     match uu____13455 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13419 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13472,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13474;
                          FStar_Syntax_Syntax.lbtyp = uu____13475;
                          FStar_Syntax_Syntax.lbeff = uu____13476;
                          FStar_Syntax_Syntax.lbdef = uu____13477;_}::[]),uu____13478,uu____13479,uu____13480)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13496 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13496 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let valid_b2t_x =
                 let uu____13514 =
                   let uu____13518 =
                     let uu____13520 =
                       FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
                     [uu____13520] in
                   ("Valid", uu____13518) in
                 FStar_SMTEncoding_Util.mkApp uu____13514 in
               let decls =
                 let uu____13525 =
                   let uu____13527 =
                     let uu____13528 =
                       let uu____13532 =
                         let uu____13533 =
                           let uu____13539 =
                             let uu____13540 =
                               let uu____13543 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13543) in
                             FStar_SMTEncoding_Util.mkEq uu____13540 in
                           ([[valid_b2t_x]], [xx], uu____13539) in
                         FStar_SMTEncoding_Util.mkForall uu____13533 in
                       (uu____13532, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Term.Assume uu____13528 in
                   [uu____13527] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13525 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let
          (uu____13560,uu____13561,quals,uu____13563) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___128_13571  ->
                  match uu___128_13571 with
                  | FStar_Syntax_Syntax.Discriminator uu____13572 -> true
                  | uu____13573 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13575,lids,quals,uu____13578) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13587 =
                     let uu____13588 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13588.FStar_Ident.idText in
                   uu____13587 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___129_13590  ->
                     match uu___129_13590 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13591 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13594,quals,uu____13596) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___130_13608  ->
                  match uu___130_13608 with
                  | FStar_Syntax_Syntax.Projector uu____13609 -> true
                  | uu____13612 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13619 = try_lookup_free_var env l in
          (match uu____13619 with
           | Some uu____13623 -> ([], env)
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
          ((is_rec,bindings),uu____13632,quals,uu____13634) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13648,uu____13649) ->
          let uu____13656 = encode_signature env ses in
          (match uu____13656 with
           | (g,env1) ->
               let uu____13666 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___131_13676  ->
                         match uu___131_13676 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13677,Some "inversion axiom",uu____13678)
                             -> false
                         | uu____13680 -> true)) in
               (match uu____13666 with
                | (g',inversions) ->
                    let uu____13689 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___132_13699  ->
                              match uu___132_13699 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13700 ->
                                  true
                              | uu____13706 -> false)) in
                    (match uu____13689 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13717,tps,k,uu____13720,datas,quals) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___133_13731  ->
                    match uu___133_13731 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13732 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13739 = c in
              match uu____13739 with
              | (name,args,uu____13743,uu____13744,uu____13745) ->
                  let uu____13748 =
                    let uu____13749 =
                      let uu____13755 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13762  ->
                                match uu____13762 with
                                | (uu____13766,sort,uu____13768) -> sort)) in
                      (name, uu____13755, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13749 in
                  [uu____13748]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13786 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13789 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13789 FStar_Option.isNone)) in
            if uu____13786
            then []
            else
              (let uu____13806 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13806 with
               | (xxsym,xx) ->
                   let uu____13812 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13823  ->
                             fun l  ->
                               match uu____13823 with
                               | (out,decls) ->
                                   let uu____13835 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13835 with
                                    | (uu____13841,data_t) ->
                                        let uu____13843 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13843 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13872 =
                                                 let uu____13873 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13873.FStar_Syntax_Syntax.n in
                                               match uu____13872 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13881,indices) ->
                                                   indices
                                               | uu____13897 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13909  ->
                                                         match uu____13909
                                                         with
                                                         | (x,uu____13913) ->
                                                             let uu____13914
                                                               =
                                                               let uu____13915
                                                                 =
                                                                 let uu____13919
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13919,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13915 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13914)
                                                    env) in
                                             let uu____13921 =
                                               encode_args indices env1 in
                                             (match uu____13921 with
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
                                                      let uu____13941 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13949
                                                                 =
                                                                 let uu____13952
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13952,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13949)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13941
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13954 =
                                                      let uu____13955 =
                                                        let uu____13958 =
                                                          let uu____13959 =
                                                            let uu____13962 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13962,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13959 in
                                                        (out, uu____13958) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13955 in
                                                    (uu____13954,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13812 with
                    | (data_ax,decls) ->
                        let uu____13970 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13970 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13981 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13981 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13984 =
                                 let uu____13988 =
                                   let uu____13989 =
                                     let uu____13995 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14003 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13995,
                                       uu____14003) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13989 in
                                 let uu____14011 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13988, (Some "inversion axiom"),
                                   uu____14011) in
                               FStar_SMTEncoding_Term.Assume uu____13984 in
                             let pattern_guarded_inversion =
                               let uu____14015 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14015
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14023 =
                                   let uu____14024 =
                                     let uu____14028 =
                                       let uu____14029 =
                                         let uu____14035 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14043 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14035, uu____14043) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14029 in
                                     let uu____14051 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14028, (Some "inversion axiom"),
                                       uu____14051) in
                                   FStar_SMTEncoding_Term.Assume uu____14024 in
                                 [uu____14023]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14054 =
            let uu____14062 =
              let uu____14063 = FStar_Syntax_Subst.compress k in
              uu____14063.FStar_Syntax_Syntax.n in
            match uu____14062 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14092 -> (tps, k) in
          (match uu____14054 with
           | (formals,res) ->
               let uu____14107 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14107 with
                | (formals1,res1) ->
                    let uu____14114 = encode_binders None formals1 env in
                    (match uu____14114 with
                     | (vars,guards,env',binder_decls,uu____14129) ->
                         let uu____14136 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14136 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14149 =
                                  let uu____14153 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14153) in
                                FStar_SMTEncoding_Util.mkApp uu____14149 in
                              let uu____14158 =
                                let tname_decl =
                                  let uu____14164 =
                                    let uu____14165 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14180  ->
                                              match uu____14180 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14188 = varops.next_id () in
                                    (tname, uu____14165,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14188, false) in
                                  constructor_or_logic_type_decl uu____14164 in
                                let uu____14193 =
                                  match vars with
                                  | [] ->
                                      let uu____14200 =
                                        let uu____14201 =
                                          let uu____14203 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14203 in
                                        push_free_var env1 t tname
                                          uu____14201 in
                                      ([], uu____14200)
                                  | uu____14207 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14213 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14213 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14222 =
                                          let uu____14226 =
                                            let uu____14227 =
                                              let uu____14235 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14235) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14227 in
                                          (uu____14226,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____14222 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14193 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14158 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14258 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14258 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14272 =
                                               let uu____14273 =
                                                 let uu____14277 =
                                                   let uu____14278 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14278 in
                                                 (uu____14277,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14273 in
                                             [uu____14272]
                                           else [] in
                                         let uu____14281 =
                                           let uu____14283 =
                                             let uu____14285 =
                                               let uu____14286 =
                                                 let uu____14290 =
                                                   let uu____14291 =
                                                     let uu____14297 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14297) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14291 in
                                                 (uu____14290, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14286 in
                                             [uu____14285] in
                                           FStar_List.append karr uu____14283 in
                                         FStar_List.append decls1 uu____14281 in
                                   let aux =
                                     let uu____14306 =
                                       let uu____14308 =
                                         inversion_axioms tapp vars in
                                       let uu____14310 =
                                         let uu____14312 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14312] in
                                       FStar_List.append uu____14308
                                         uu____14310 in
                                     FStar_List.append kindingAx uu____14306 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14317,uu____14318,uu____14319,uu____14320,uu____14321,uu____14322)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14329,t,uu____14331,n_tps,quals,uu____14334) ->
          let uu____14339 = new_term_constant_and_tok_from_lid env d in
          (match uu____14339 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14350 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14350 with
                | (formals,t_res) ->
                    let uu____14372 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14372 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14381 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14381 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14419 =
                                            mk_term_projector_name d x in
                                          (uu____14419,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14421 =
                                  let uu____14431 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14431, true) in
                                FStar_All.pipe_right uu____14421
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
                              let uu____14453 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14453 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14461::uu____14462 ->
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
                                         let uu____14487 =
                                           let uu____14493 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14493) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14487
                                     | uu____14506 -> tok_typing in
                                   let uu____14511 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14511 with
                                    | (vars',guards',env'',decls_formals,uu____14526)
                                        ->
                                        let uu____14533 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14533 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14552 ->
                                                   let uu____14556 =
                                                     let uu____14557 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14557 in
                                                   [uu____14556] in
                                             let encode_elim uu____14564 =
                                               let uu____14565 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14565 with
                                               | (head1,args) ->
                                                   let uu____14594 =
                                                     let uu____14595 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14595.FStar_Syntax_Syntax.n in
                                                   (match uu____14594 with
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
                                                        let uu____14613 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14613
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
                                                                 | uu____14639
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14647
                                                                    =
                                                                    let uu____14648
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14648 in
                                                                    if
                                                                    uu____14647
                                                                    then
                                                                    let uu____14655
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14655]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14657
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14670
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14670
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14692
                                                                    =
                                                                    let uu____14696
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14696 in
                                                                    (match uu____14692
                                                                    with
                                                                    | 
                                                                    (uu____14703,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14709
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14709
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14711
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14711
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
                                                             (match uu____14657
                                                              with
                                                              | (uu____14719,arg_vars,elim_eqns_or_guards,uu____14722)
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
                                                                    let uu____14741
                                                                    =
                                                                    let uu____14745
                                                                    =
                                                                    let uu____14746
                                                                    =
                                                                    let uu____14752
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14758
                                                                    =
                                                                    let uu____14759
                                                                    =
                                                                    let uu____14762
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14762) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14759 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14752,
                                                                    uu____14758) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14746 in
                                                                    (uu____14745,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14741 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14775
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14775,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14777
                                                                    =
                                                                    let uu____14781
                                                                    =
                                                                    let uu____14782
                                                                    =
                                                                    let uu____14788
                                                                    =
                                                                    let uu____14791
                                                                    =
                                                                    let uu____14793
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14793] in
                                                                    [uu____14791] in
                                                                    let uu____14796
                                                                    =
                                                                    let uu____14797
                                                                    =
                                                                    let uu____14800
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14801
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14800,
                                                                    uu____14801) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14797 in
                                                                    (uu____14788,
                                                                    [x],
                                                                    uu____14796) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14782 in
                                                                    let uu____14811
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14781,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14811) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14777
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14816
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
                                                                    (let uu____14831
                                                                    =
                                                                    let uu____14832
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14832
                                                                    dapp1 in
                                                                    [uu____14831]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14816
                                                                    FStar_List.flatten in
                                                                    let uu____14836
                                                                    =
                                                                    let uu____14840
                                                                    =
                                                                    let uu____14841
                                                                    =
                                                                    let uu____14847
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14853
                                                                    =
                                                                    let uu____14854
                                                                    =
                                                                    let uu____14857
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14857) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14854 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14847,
                                                                    uu____14853) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14841 in
                                                                    (uu____14840,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14836) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14867 ->
                                                        ((let uu____14869 =
                                                            let uu____14870 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14871 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14870
                                                              uu____14871 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14869);
                                                         ([], []))) in
                                             let uu____14874 = encode_elim () in
                                             (match uu____14874 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14886 =
                                                      let uu____14888 =
                                                        let uu____14890 =
                                                          let uu____14892 =
                                                            let uu____14894 =
                                                              let uu____14895
                                                                =
                                                                let uu____14901
                                                                  =
                                                                  let uu____14903
                                                                    =
                                                                    let uu____14904
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14904 in
                                                                  Some
                                                                    uu____14903 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14901) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14895 in
                                                            [uu____14894] in
                                                          let uu____14907 =
                                                            let uu____14909 =
                                                              let uu____14911
                                                                =
                                                                let uu____14913
                                                                  =
                                                                  let uu____14915
                                                                    =
                                                                    let uu____14917
                                                                    =
                                                                    let uu____14919
                                                                    =
                                                                    let uu____14920
                                                                    =
                                                                    let uu____14924
                                                                    =
                                                                    let uu____14925
                                                                    =
                                                                    let uu____14931
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14931) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14925 in
                                                                    (uu____14924,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14920 in
                                                                    let uu____14938
                                                                    =
                                                                    let uu____14940
                                                                    =
                                                                    let uu____14941
                                                                    =
                                                                    let uu____14945
                                                                    =
                                                                    let uu____14946
                                                                    =
                                                                    let uu____14952
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14958
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14952,
                                                                    uu____14958) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14946 in
                                                                    (uu____14945,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14941 in
                                                                    [uu____14940] in
                                                                    uu____14919
                                                                    ::
                                                                    uu____14938 in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14917 in
                                                                  FStar_List.append
                                                                    uu____14915
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14913 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14911 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14909 in
                                                          FStar_List.append
                                                            uu____14892
                                                            uu____14907 in
                                                        FStar_List.append
                                                          decls3 uu____14890 in
                                                      FStar_List.append
                                                        decls2 uu____14888 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14886 in
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
           (fun uu____14979  ->
              fun se  ->
                match uu____14979 with
                | (g,env1) ->
                    let uu____14991 = encode_sigelt env1 se in
                    (match uu____14991 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15027 =
        match uu____15027 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15045 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____15050 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15050
                   then
                     let uu____15051 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15052 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15053 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15051 uu____15052 uu____15053
                   else ());
                  (let uu____15055 = encode_term t1 env1 in
                   match uu____15055 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15065 =
                         let uu____15069 =
                           let uu____15070 =
                             let uu____15071 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15071
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15070 in
                         new_term_constant_from_string env1 x uu____15069 in
                       (match uu____15065 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15082 = FStar_Options.log_queries () in
                              if uu____15082
                              then
                                let uu____15084 =
                                  let uu____15085 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15086 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15087 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15085 uu____15086 uu____15087 in
                                Some uu____15084
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15098,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15107 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15107 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____15126 = encode_sigelt env1 se in
                 (match uu____15126 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15136 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15136 with | (uu____15148,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15193  ->
            match uu____15193 with
            | (l,uu____15200,uu____15201) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15222  ->
            match uu____15222 with
            | (l,uu____15230,uu____15231) ->
                let uu____15236 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____15237 =
                  let uu____15239 =
                    let uu____15240 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15240 in
                  [uu____15239] in
                uu____15236 :: uu____15237)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15251 =
      let uu____15253 =
        let uu____15254 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15266 =
          let uu____15267 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15267 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15254;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15266
        } in
      [uu____15253] in
    FStar_ST.write last_env uu____15251
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15277 = FStar_ST.read last_env in
      match uu____15277 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15283 ->
          let uu___161_15285 = e in
          let uu____15286 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___161_15285.bindings);
            depth = (uu___161_15285.depth);
            tcenv;
            warn = (uu___161_15285.warn);
            cache = (uu___161_15285.cache);
            nolabels = (uu___161_15285.nolabels);
            use_zfuel_name = (uu___161_15285.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___161_15285.encode_non_total_function_typ);
            current_module_name = uu____15286
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15290 = FStar_ST.read last_env in
    match uu____15290 with
    | [] -> failwith "Empty env stack"
    | uu____15295::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15303  ->
    let uu____15304 = FStar_ST.read last_env in
    match uu____15304 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___162_15325 = hd1 in
          {
            bindings = (uu___162_15325.bindings);
            depth = (uu___162_15325.depth);
            tcenv = (uu___162_15325.tcenv);
            warn = (uu___162_15325.warn);
            cache = refs;
            nolabels = (uu___162_15325.nolabels);
            use_zfuel_name = (uu___162_15325.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_15325.encode_non_total_function_typ);
            current_module_name = (uu___162_15325.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15331  ->
    let uu____15332 = FStar_ST.read last_env in
    match uu____15332 with
    | [] -> failwith "Popping an empty stack"
    | uu____15337::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15345  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15348  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15351  ->
    let uu____15352 = FStar_ST.read last_env in
    match uu____15352 with
    | hd1::uu____15358::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15364 -> failwith "Impossible"
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
        let uu____15409 = FStar_Options.log_queries () in
        if uu____15409
        then
          let uu____15411 =
            let uu____15412 =
              let uu____15413 =
                let uu____15414 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15414 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15413 in
            FStar_SMTEncoding_Term.Caption uu____15412 in
          uu____15411 :: decls
        else decls in
      let env =
        let uu____15421 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15421 tcenv in
      let uu____15422 = encode_sigelt env se in
      match uu____15422 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15428 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15428))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15439 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15439
       then
         let uu____15440 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15440
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let uu____15445 =
         encode_signature
           (let uu___163_15449 = env in
            {
              bindings = (uu___163_15449.bindings);
              depth = (uu___163_15449.depth);
              tcenv = (uu___163_15449.tcenv);
              warn = false;
              cache = (uu___163_15449.cache);
              nolabels = (uu___163_15449.nolabels);
              use_zfuel_name = (uu___163_15449.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___163_15449.encode_non_total_function_typ);
              current_module_name = (uu___163_15449.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15445 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15461 = FStar_Options.log_queries () in
             if uu____15461
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___164_15466 = env1 in
               {
                 bindings = (uu___164_15466.bindings);
                 depth = (uu___164_15466.depth);
                 tcenv = (uu___164_15466.tcenv);
                 warn = true;
                 cache = (uu___164_15466.cache);
                 nolabels = (uu___164_15466.nolabels);
                 use_zfuel_name = (uu___164_15466.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___164_15466.encode_non_total_function_typ);
                 current_module_name = (uu___164_15466.current_module_name)
               });
            (let uu____15468 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15468
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
        (let uu____15503 =
           let uu____15504 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15504.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15503);
        (let env =
           let uu____15506 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15506 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15513 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15534 = aux rest in
                 (match uu____15534 with
                  | (out,rest1) ->
                      let t =
                        let uu____15552 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15552 with
                        | Some uu____15556 ->
                            let uu____15557 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15557
                              x.FStar_Syntax_Syntax.sort
                        | uu____15558 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15561 =
                        let uu____15563 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___165_15564 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___165_15564.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___165_15564.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15563 :: out in
                      (uu____15561, rest1))
             | uu____15567 -> ([], bindings1) in
           let uu____15571 = aux bindings in
           match uu____15571 with
           | (closing,bindings1) ->
               let uu____15585 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15585, bindings1) in
         match uu____15513 with
         | (q1,bindings1) ->
             let uu____15598 =
               let uu____15601 =
                 FStar_List.filter
                   (fun uu___134_15603  ->
                      match uu___134_15603 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15604 ->
                          false
                      | uu____15608 -> true) bindings1 in
               encode_env_bindings env uu____15601 in
             (match uu____15598 with
              | (env_decls,env1) ->
                  ((let uu____15619 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15619
                    then
                      let uu____15620 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15620
                    else ());
                   (let uu____15622 = encode_formula q1 env1 in
                    match uu____15622 with
                    | (phi,qdecls) ->
                        let uu____15634 =
                          let uu____15637 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15637 phi in
                        (match uu____15634 with
                         | (labels,phi1) ->
                             let uu____15647 = encode_labels labels in
                             (match uu____15647 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15668 =
                                      let uu____15672 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15673 =
                                        varops.mk_unique "@query" in
                                      (uu____15672, (Some "query"),
                                        uu____15673) in
                                    FStar_SMTEncoding_Term.Assume uu____15668 in
                                  let suffix =
                                    let uu____15677 =
                                      let uu____15679 =
                                        let uu____15681 =
                                          FStar_Options.print_z3_statistics
                                            () in
                                        if uu____15681
                                        then
                                          [FStar_SMTEncoding_Term.PrintStats]
                                        else [] in
                                      FStar_List.append uu____15679
                                        [FStar_SMTEncoding_Term.Echo "Done!"] in
                                    FStar_List.append label_suffix
                                      uu____15677 in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15693 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15693 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15695 = encode_formula q env in
       match uu____15695 with
       | (f,uu____15699) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15701) -> true
             | uu____15704 -> false)))
