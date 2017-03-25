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
  encode_non_total_function_typ: Prims.bool;}
let print_env: env_t -> Prims.string =
  fun e  ->
    let uu____945 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___112_949  ->
              match uu___112_949 with
              | Binding_var (x,uu____951) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____953,uu____954,uu____955) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____945 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option
  =
  fun env  ->
    fun t  ->
      let uu____988 = FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____988
      then
        let uu____990 = FStar_Syntax_Print.term_to_string t in Some uu____990
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1001 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1001)
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
        (let uu___137_1013 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___137_1013.tcenv);
           warn = (uu___137_1013.warn);
           cache = (uu___137_1013.cache);
           nolabels = (uu___137_1013.nolabels);
           use_zfuel_name = (uu___137_1013.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___137_1013.encode_non_total_function_typ)
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
        (let uu___138_1026 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___138_1026.depth);
           tcenv = (uu___138_1026.tcenv);
           warn = (uu___138_1026.warn);
           cache = (uu___138_1026.cache);
           nolabels = (uu___138_1026.nolabels);
           use_zfuel_name = (uu___138_1026.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___138_1026.encode_non_total_function_typ)
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
          (let uu___139_1042 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___139_1042.depth);
             tcenv = (uu___139_1042.tcenv);
             warn = (uu___139_1042.warn);
             cache = (uu___139_1042.cache);
             nolabels = (uu___139_1042.nolabels);
             use_zfuel_name = (uu___139_1042.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___139_1042.encode_non_total_function_typ)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___140_1052 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___140_1052.depth);
          tcenv = (uu___140_1052.tcenv);
          warn = (uu___140_1052.warn);
          cache = (uu___140_1052.cache);
          nolabels = (uu___140_1052.nolabels);
          use_zfuel_name = (uu___140_1052.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___140_1052.encode_non_total_function_typ)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___113_1068  ->
             match uu___113_1068 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1076 -> None) in
      let uu____1079 = aux a in
      match uu____1079 with
      | None  ->
          let a2 = unmangle a in
          let uu____1086 = aux a2 in
          (match uu____1086 with
           | None  ->
               let uu____1092 =
                 let uu____1093 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1094 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1093 uu____1094 in
               failwith uu____1092
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1114 =
        let uu___141_1115 = env in
        let uu____1116 =
          let uu____1118 =
            let uu____1119 =
              let uu____1126 =
                let uu____1128 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1128 in
              (x, fname, uu____1126, None) in
            Binding_fvar uu____1119 in
          uu____1118 :: (env.bindings) in
        {
          bindings = uu____1116;
          depth = (uu___141_1115.depth);
          tcenv = (uu___141_1115.tcenv);
          warn = (uu___141_1115.warn);
          cache = (uu___141_1115.cache);
          nolabels = (uu___141_1115.nolabels);
          use_zfuel_name = (uu___141_1115.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___141_1115.encode_non_total_function_typ)
        } in
      (fname, ftok, uu____1114)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___114_1150  ->
           match uu___114_1150 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1172 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1184 =
        lookup_binding env
          (fun uu___115_1186  ->
             match uu___115_1186 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1196 -> None) in
      FStar_All.pipe_right uu____1184 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1209 = try_lookup_lid env a in
      match uu____1209 with
      | None  ->
          let uu____1226 =
            let uu____1227 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1227 in
          failwith uu____1226
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
          let uu___142_1258 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___142_1258.depth);
            tcenv = (uu___142_1258.tcenv);
            warn = (uu___142_1258.warn);
            cache = (uu___142_1258.cache);
            nolabels = (uu___142_1258.nolabels);
            use_zfuel_name = (uu___142_1258.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___142_1258.encode_non_total_function_typ)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1270 = lookup_lid env x in
        match uu____1270 with
        | (t1,t2,uu____1278) ->
            let t3 =
              let uu____1284 =
                let uu____1288 =
                  let uu____1290 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1290] in
                (f, uu____1288) in
              FStar_SMTEncoding_Util.mkApp uu____1284 in
            let uu___143_1293 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___143_1293.depth);
              tcenv = (uu___143_1293.tcenv);
              warn = (uu___143_1293.warn);
              cache = (uu___143_1293.cache);
              nolabels = (uu___143_1293.nolabels);
              use_zfuel_name = (uu___143_1293.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___143_1293.encode_non_total_function_typ)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1303 = try_lookup_lid env l in
      match uu____1303 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1330 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1335,fuel::[]) ->
                         let uu____1338 =
                           let uu____1339 =
                             let uu____1340 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1340 Prims.fst in
                           FStar_Util.starts_with uu____1339 "fuel" in
                         if uu____1338
                         then
                           let uu____1342 =
                             let uu____1343 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1343
                               fuel in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1342
                         else Some t
                     | uu____1346 -> Some t)
                | uu____1347 -> None))
let lookup_free_var env a =
  let uu____1365 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1365 with
  | Some t -> t
  | None  ->
      let uu____1368 =
        let uu____1369 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1369 in
      failwith uu____1368
let lookup_free_var_name env a =
  let uu____1386 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1386 with | (x,uu____1393,uu____1394) -> x
let lookup_free_var_sym env a =
  let uu____1418 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1418 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1439;
             FStar_SMTEncoding_Term.rng = uu____1440;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1448 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1462 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___116_1471  ->
           match uu___116_1471 with
           | Binding_fvar (uu____1473,nm',tok,uu____1476) when nm = nm' ->
               tok
           | uu____1481 -> None)
let mkForall_fuel' n1 uu____1498 =
  match uu____1498 with
  | (pats,vars,body) ->
      let fallback uu____1514 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1517 = FStar_Options.unthrottle_inductives () in
      if uu____1517
      then fallback ()
      else
        (let uu____1519 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1519 with
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
                       | uu____1538 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1552 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1552
                     | uu____1554 ->
                         let uu____1555 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1555 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1558 -> body in
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
          let uu____1602 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1602 FStar_Option.isNone
      | uu____1615 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1622 =
        let uu____1623 = FStar_Syntax_Util.un_uinst t in
        uu____1623.FStar_Syntax_Syntax.n in
      match uu____1622 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1626,uu____1627,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___117_1656  ->
                  match uu___117_1656 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1657 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1658,uu____1659,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1686 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1686 FStar_Option.isSome
      | uu____1699 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1706 = head_normal env t in
      if uu____1706
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
    let uu____1717 =
      let uu____1721 = FStar_Syntax_Syntax.null_binder t in [uu____1721] in
    let uu____1722 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1717 uu____1722 None
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
                    let uu____1749 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1749
                | s ->
                    let uu____1752 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1752) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___118_1764  ->
    match uu___118_1764 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1765 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____1793;
                       FStar_SMTEncoding_Term.rng = uu____1794;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              aux f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1808) ->
              let uu____1813 =
                ((FStar_List.length args) = (FStar_List.length vars)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1823 -> false) args vars) in
              if uu____1813 then tok_of_name env f else None
          | (uu____1826,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t1 in
              let uu____1829 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1831 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1831)) in
              if uu____1829 then Some t1 else None
          | uu____1834 -> None in
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
      (let uu____1849 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____1849
       then
         let uu____1850 = FStar_Syntax_Print.term_to_string tm in
         let uu____1851 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____1850 uu____1851
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
    | uu____1933 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___119_1936  ->
    match uu___119_1936 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____1938 =
          let uu____1942 =
            let uu____1944 =
              let uu____1945 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____1945 in
            [uu____1944] in
          ("FStar.Char.Char", uu____1942) in
        FStar_SMTEncoding_Util.mkApp uu____1938
    | FStar_Const.Const_int (i,None ) ->
        let uu____1953 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____1953
    | FStar_Const.Const_int (i,Some uu____1955) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____1964) ->
        let uu____1967 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____1967
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____1971 =
          let uu____1972 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____1972 in
        failwith uu____1971
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1991 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1999 ->
            let uu____2004 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2004
        | uu____2005 ->
            if norm1
            then let uu____2006 = whnf env t1 in aux false uu____2006
            else
              (let uu____2008 =
                 let uu____2009 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2010 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2009 uu____2010 in
               failwith uu____2008) in
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
    | uu____2031 ->
        let uu____2032 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2032)
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
        (let uu____2175 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2175
         then
           let uu____2176 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2176
         else ());
        (let uu____2178 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2214  ->
                   fun b  ->
                     match uu____2214 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2257 =
                           let x = unmangle (Prims.fst b) in
                           let uu____2266 = gen_term_var env1 x in
                           match uu____2266 with
                           | (xxsym,xx,env') ->
                               let uu____2280 =
                                 let uu____2283 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2283 env1 xx in
                               (match uu____2280 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2257 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2178 with
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
          let uu____2371 = encode_term t env in
          match uu____2371 with
          | (t1,decls) ->
              let uu____2378 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2378, decls)
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
          let uu____2386 = encode_term t env in
          match uu____2386 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2395 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2395, decls)
               | Some f ->
                   let uu____2397 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2397, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2404 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2404
       then
         let uu____2405 = FStar_Syntax_Print.tag_of_term t in
         let uu____2406 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2407 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2405 uu____2406
           uu____2407
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2412 =
             let uu____2413 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2414 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2415 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2416 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2413
               uu____2414 uu____2415 uu____2416 in
           failwith uu____2412
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2420 =
             let uu____2421 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2421 in
           failwith uu____2420
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2426) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2446) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2455 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2455, [])
       | FStar_Syntax_Syntax.Tm_type uu____2461 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2464) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2470 = encode_const c in (uu____2470, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let uu____2484 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2484 with
            | (binders1,res) ->
                let uu____2491 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2491
                then
                  let uu____2494 = encode_binders None binders1 env in
                  (match uu____2494 with
                   | (vars,guards,env',decls,uu____2509) ->
                       let fsym =
                         let uu____2519 = varops.fresh "f" in
                         (uu____2519, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2522 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___144_2526 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___144_2526.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___144_2526.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___144_2526.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___144_2526.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___144_2526.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___144_2526.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___144_2526.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___144_2526.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___144_2526.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___144_2526.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___144_2526.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___144_2526.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___144_2526.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___144_2526.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___144_2526.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___144_2526.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___144_2526.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___144_2526.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___144_2526.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___144_2526.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___144_2526.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___144_2526.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___144_2526.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2522 with
                        | (pre_opt,res_t) ->
                            let uu____2533 =
                              encode_term_pred None res_t env' app in
                            (match uu____2533 with
                             | (res_pred,decls') ->
                                 let uu____2540 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2547 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2547, [])
                                   | Some pre ->
                                       let uu____2550 =
                                         encode_formula pre env' in
                                       (match uu____2550 with
                                        | (guard,decls0) ->
                                            let uu____2558 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2558, decls0)) in
                                 (match uu____2540 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2566 =
                                          let uu____2572 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2572) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2566 in
                                      let cvars =
                                        let uu____2582 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2582
                                          (FStar_List.filter
                                             (fun uu____2588  ->
                                                match uu____2588 with
                                                | (x,uu____2592) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2603 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2603 with
                                       | Some (t',sorts,uu____2619) ->
                                           let uu____2629 =
                                             let uu____2630 =
                                               let uu____2634 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               (t', uu____2634) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2630 in
                                           (uu____2629, [])
                                       | None  ->
                                           let tsym =
                                             let uu____2650 =
                                               let uu____2651 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2651 in
                                             varops.mk_unique uu____2650 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2658 =
                                               FStar_Options.log_queries () in
                                             if uu____2658
                                             then
                                               let uu____2660 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2660
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2666 =
                                               let uu____2670 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2670) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2666 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Some
                                                 (Prims.strcat "kinding_"
                                                    tsym) in
                                             let uu____2679 =
                                               let uu____2684 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2684, a_name, a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2679 in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1 in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1 in
                                           let pre_typing =
                                             let a_name =
                                               Some
                                                 (Prims.strcat "pre_typing_"
                                                    tsym) in
                                             let uu____2699 =
                                               let uu____2704 =
                                                 let uu____2705 =
                                                   let uu____2711 =
                                                     let uu____2712 =
                                                       let uu____2715 =
                                                         let uu____2716 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2716 in
                                                       (f_has_t, uu____2715) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2712 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2711) in
                                                 mkForall_fuel uu____2705 in
                                               (uu____2704,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2699 in
                                           let t_interp1 =
                                             let a_name =
                                               Some
                                                 (Prims.strcat
                                                    "interpretation_" tsym) in
                                             let uu____2731 =
                                               let uu____2736 =
                                                 let uu____2737 =
                                                   let uu____2743 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2743) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2737 in
                                               (uu____2736, a_name, a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2731 in
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
                       Some (Prims.strcat "non_total_function_typing_" tsym) in
                     let uu____2776 =
                       let uu____2781 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____2781, (Some "Typing for non-total arrows"),
                         a_name) in
                     FStar_SMTEncoding_Term.Assume uu____2776 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Some (Prims.strcat "pre_typing_" tsym) in
                     let uu____2792 =
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
                       (uu____2797, a_name, a_name) in
                     FStar_SMTEncoding_Term.Assume uu____2792 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2824 ->
           let uu____2829 =
             let uu____2832 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2832 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2837;
                 FStar_Syntax_Syntax.pos = uu____2838;
                 FStar_Syntax_Syntax.vars = uu____2839;_} ->
                 let uu____2846 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2846 with
                  | (b,f1) ->
                      let uu____2860 =
                        let uu____2861 = FStar_List.hd b in
                        Prims.fst uu____2861 in
                      (uu____2860, f1))
             | uu____2866 -> failwith "impossible" in
           (match uu____2829 with
            | (x,f) ->
                let uu____2873 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____2873 with
                 | (base_t,decls) ->
                     let uu____2880 = gen_term_var env x in
                     (match uu____2880 with
                      | (x1,xtm,env') ->
                          let uu____2889 = encode_formula f env' in
                          (match uu____2889 with
                           | (refinement,decls') ->
                               let uu____2896 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____2896 with
                                | (fsym,fterm) ->
                                    let encoding =
                                      let uu____2904 =
                                        let uu____2907 =
                                          FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                            (Some fterm) xtm base_t in
                                        (uu____2907, refinement) in
                                      FStar_SMTEncoding_Util.mkAnd uu____2904 in
                                    let cvars =
                                      let uu____2912 =
                                        FStar_SMTEncoding_Term.free_variables
                                          encoding in
                                      FStar_All.pipe_right uu____2912
                                        (FStar_List.filter
                                           (fun uu____2918  ->
                                              match uu____2918 with
                                              | (y,uu____2922) ->
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
                                    let uu____2941 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2941 with
                                     | Some (t1,uu____2956,uu____2957) ->
                                         let uu____2967 =
                                           let uu____2968 =
                                             let uu____2972 =
                                               FStar_All.pipe_right cvars
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             (t1, uu____2972) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2968 in
                                         (uu____2967, [])
                                     | None  ->
                                         let tsym =
                                           let uu____2988 =
                                             let uu____2989 =
                                               FStar_Util.digest_of_string
                                                 tkey_hash in
                                             Prims.strcat "Tm_refine_"
                                               uu____2989 in
                                           varops.mk_unique uu____2988 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____2998 =
                                             let uu____3002 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars in
                                             (tsym, uu____3002) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2998 in
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
                                           let uu____3012 =
                                             let uu____3017 =
                                               let uu____3018 =
                                                 let uu____3024 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars,
                                                   uu____3024) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3018 in
                                             (uu____3017,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Some
                                                  (Prims.strcat "haseq" tsym))) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3012 in
                                         let t_kinding =
                                           let uu____3035 =
                                             let uu____3040 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars,
                                                   t_has_kind) in
                                             (uu____3040,
                                               (Some "refinement kinding"),
                                               (Some
                                                  (Prims.strcat
                                                     "refinement_kinding_"
                                                     tsym))) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3035 in
                                         let t_interp =
                                           let uu____3051 =
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
                                               (Some
                                                  (Prims.strcat
                                                     "refinement_interpretation_"
                                                     tsym))) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3051 in
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
             let uu____3106 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3106 in
           let uu____3110 = encode_term_pred None k env ttm in
           (match uu____3110 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3118 =
                    let uu____3123 =
                      let uu____3125 =
                        let uu____3126 =
                          let uu____3127 =
                            let uu____3128 = FStar_Unionfind.uvar_id uv in
                            FStar_All.pipe_left FStar_Util.string_of_int
                              uu____3128 in
                          FStar_Util.format1 "uvar_typing_%s" uu____3127 in
                        varops.mk_unique uu____3126 in
                      Some uu____3125 in
                    (t_has_k, (Some "Uvar typing"), uu____3123) in
                  FStar_SMTEncoding_Term.Assume uu____3118 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3135 ->
           let uu____3145 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3145 with
            | (head1,args_e) ->
                let uu____3173 =
                  let uu____3181 =
                    let uu____3182 = FStar_Syntax_Subst.compress head1 in
                    uu____3182.FStar_Syntax_Syntax.n in
                  (uu____3181, args_e) in
                (match uu____3173 with
                 | (uu____3192,uu____3193) when head_redex env head1 ->
                     let uu____3204 = whnf env t in
                     encode_term uu____3204 env
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
                     let uu____3278 = encode_term v1 env in
                     (match uu____3278 with
                      | (v11,decls1) ->
                          let uu____3285 = encode_term v2 env in
                          (match uu____3285 with
                           | (v21,decls2) ->
                               let uu____3292 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3292,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3294) ->
                     let e0 =
                       let uu____3308 =
                         let uu____3311 =
                           let uu____3312 =
                             let uu____3322 =
                               let uu____3328 = FStar_List.hd args_e in
                               [uu____3328] in
                             (head1, uu____3322) in
                           FStar_Syntax_Syntax.Tm_app uu____3312 in
                         FStar_Syntax_Syntax.mk uu____3311 in
                       uu____3308 None head1.FStar_Syntax_Syntax.pos in
                     ((let uu____3361 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3361
                       then
                         let uu____3362 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Trying to normalize %s\n"
                           uu____3362
                       else ());
                      (let e01 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Reify;
                           FStar_TypeChecker_Normalize.Eager_unfolding;
                           FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                           env.tcenv e0 in
                       (let uu____3366 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify") in
                        if uu____3366
                        then
                          let uu____3367 =
                            FStar_Syntax_Print.term_to_string e01 in
                          FStar_Util.print1 "Result of normalization %s\n"
                            uu____3367
                        else ());
                       (let e02 =
                          let uu____3370 =
                            let uu____3371 =
                              let uu____3372 =
                                FStar_Syntax_Subst.compress e01 in
                              uu____3372.FStar_Syntax_Syntax.n in
                            match uu____3371 with
                            | FStar_Syntax_Syntax.Tm_app uu____3375 -> false
                            | uu____3385 -> true in
                          if uu____3370
                          then e01
                          else
                            (let uu____3387 =
                               FStar_Syntax_Util.head_and_args e01 in
                             match uu____3387 with
                             | (head2,args) ->
                                 let uu____3413 =
                                   let uu____3414 =
                                     let uu____3415 =
                                       FStar_Syntax_Subst.compress head2 in
                                     uu____3415.FStar_Syntax_Syntax.n in
                                   match uu____3414 with
                                   | FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_reify ) -> true
                                   | uu____3418 -> false in
                                 if uu____3413
                                 then
                                   (match args with
                                    | x::[] -> Prims.fst x
                                    | uu____3434 ->
                                        failwith
                                          "Impossible : Reify applied to multiple arguments after normalization.")
                                 else e01) in
                        let e =
                          match args_e with
                          | uu____3442::[] -> e02
                          | uu____3455 ->
                              let uu____3461 =
                                let uu____3464 =
                                  let uu____3465 =
                                    let uu____3475 = FStar_List.tl args_e in
                                    (e02, uu____3475) in
                                  FStar_Syntax_Syntax.Tm_app uu____3465 in
                                FStar_Syntax_Syntax.mk uu____3464 in
                              uu____3461 None t0.FStar_Syntax_Syntax.pos in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3498),(arg,uu____3500)::[]) -> encode_term arg env
                 | uu____3518 ->
                     let uu____3526 = encode_args args_e env in
                     (match uu____3526 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3559 = encode_term head1 env in
                            match uu____3559 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3598 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3598 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3640  ->
                                                 fun uu____3641  ->
                                                   match (uu____3640,
                                                           uu____3641)
                                                   with
                                                   | ((bv,uu____3655),
                                                      (a,uu____3657)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3671 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3671
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3676 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3676 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3686 =
                                                   let uu____3691 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3696 =
                                                     let uu____3698 =
                                                       let uu____3699 =
                                                         let uu____3700 =
                                                           let uu____3701 =
                                                             FStar_SMTEncoding_Term.hash_of_term
                                                               app_tm in
                                                           FStar_Util.digest_of_string
                                                             uu____3701 in
                                                         Prims.strcat
                                                           "partial_app_typing_"
                                                           uu____3700 in
                                                       varops.mk_unique
                                                         uu____3699 in
                                                     Some uu____3698 in
                                                   (uu____3691,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3696) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3686 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3719 = lookup_free_var_sym env fv in
                            match uu____3719 with
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
                                let uu____3757 =
                                  let uu____3758 =
                                    let uu____3761 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3761 Prims.fst in
                                  FStar_All.pipe_right uu____3758 Prims.snd in
                                Some uu____3757
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3780,FStar_Util.Inl t1,uu____3782) ->
                                Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3803,FStar_Util.Inr c,uu____3805) ->
                                Some (FStar_Syntax_Util.comp_result c)
                            | uu____3826 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3846 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3846 in
                               let uu____3847 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3847 with
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
                                     | uu____3872 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3917 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3917 with
            | (bs1,body1,opening) ->
                let fallback uu____3932 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3937 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3937, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3948 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3948
                  | FStar_Util.Inr (eff,uu____3950) ->
                      let uu____3956 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3956 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body = reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4001 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___145_4002 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___145_4002.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___145_4002.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___145_4002.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___145_4002.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___145_4002.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___145_4002.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___145_4002.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___145_4002.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___145_4002.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___145_4002.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___145_4002.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___145_4002.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___145_4002.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___145_4002.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___145_4002.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___145_4002.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___145_4002.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___145_4002.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___145_4002.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___145_4002.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___145_4002.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___145_4002.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___145_4002.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4001 FStar_Syntax_Syntax.U_unknown in
                        let uu____4003 =
                          let uu____4004 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4004 in
                        FStar_Util.Inl uu____4003
                    | FStar_Util.Inr (eff_name,uu____4011) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4042 =
                        let uu____4043 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4043 in
                      FStar_All.pipe_right uu____4042
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4055 =
                        let uu____4056 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4056 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4064 =
                          let uu____4065 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4065 in
                        FStar_All.pipe_right uu____4064
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4069 =
                             let uu____4070 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4070 in
                           FStar_All.pipe_right uu____4069
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4081 =
                         let uu____4082 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4082 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4081);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4097 =
                       (is_impure lc1) &&
                         (let uu____4098 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4098) in
                     if uu____4097
                     then fallback ()
                     else
                       (let uu____4102 = encode_binders None bs1 env in
                        match uu____4102 with
                        | (vars,guards,envbody,decls,uu____4117) ->
                            let uu____4124 =
                              let uu____4132 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4132
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4124 with
                             | (lc2,body2) ->
                                 let uu____4157 = encode_term body2 envbody in
                                 (match uu____4157 with
                                  | (body3,decls') ->
                                      let key_body =
                                        let uu____4165 =
                                          let uu____4171 =
                                            let uu____4172 =
                                              let uu____4175 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____4175, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____4172 in
                                          ([], vars, uu____4171) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4165 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____4186 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____4186 with
                                       | Some (t1,uu____4201,uu____4202) ->
                                           let uu____4212 =
                                             let uu____4213 =
                                               let uu____4217 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (t1, uu____4217) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4213 in
                                           (uu____4212, [])
                                       | None  ->
                                           let uu____4228 =
                                             is_eta env vars body3 in
                                           (match uu____4228 with
                                            | Some t1 -> (t1, [])
                                            | None  ->
                                                let cvar_sorts =
                                                  FStar_List.map Prims.snd
                                                    cvars in
                                                let fsym =
                                                  let uu____4239 =
                                                    let uu____4240 =
                                                      FStar_Util.digest_of_string
                                                        tkey_hash in
                                                    Prims.strcat "Tm_abs_"
                                                      uu____4240 in
                                                  varops.mk_unique uu____4239 in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      None) in
                                                let f =
                                                  let uu____4245 =
                                                    let uu____4249 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars in
                                                    (fsym, uu____4249) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4245 in
                                                let app = mk_Apply f vars in
                                                let typing_f =
                                                  let uu____4257 =
                                                    codomain_eff lc2 in
                                                  match uu____4257 with
                                                  | None  -> []
                                                  | Some c ->
                                                      let tfun =
                                                        FStar_Syntax_Util.arrow
                                                          bs1 c in
                                                      let uu____4264 =
                                                        encode_term_pred None
                                                          tfun env f in
                                                      (match uu____4264 with
                                                       | (f_has_t,decls'') ->
                                                           let a_name =
                                                             Some
                                                               (Prims.strcat
                                                                  "typing_"
                                                                  fsym) in
                                                           let uu____4272 =
                                                             let uu____4274 =
                                                               let uu____4275
                                                                 =
                                                                 let uu____4280
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkForall
                                                                    ([[f]],
                                                                    cvars,
                                                                    f_has_t) in
                                                                 (uu____4280,
                                                                   a_name,
                                                                   a_name) in
                                                               FStar_SMTEncoding_Term.Assume
                                                                 uu____4275 in
                                                             [uu____4274] in
                                                           FStar_List.append
                                                             decls''
                                                             uu____4272) in
                                                let interp_f =
                                                  let a_name =
                                                    Some
                                                      (Prims.strcat
                                                         "interpretation_"
                                                         fsym) in
                                                  let uu____4290 =
                                                    let uu____4295 =
                                                      let uu____4296 =
                                                        let uu____4302 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars),
                                                          uu____4302) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____4296 in
                                                    (uu____4295, a_name,
                                                      a_name) in
                                                  FStar_SMTEncoding_Term.Assume
                                                    uu____4290 in
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
           ((uu____4321,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4322;
                          FStar_Syntax_Syntax.lbunivs = uu____4323;
                          FStar_Syntax_Syntax.lbtyp = uu____4324;
                          FStar_Syntax_Syntax.lbeff = uu____4325;
                          FStar_Syntax_Syntax.lbdef = uu____4326;_}::uu____4327),uu____4328)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4346;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4348;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4364 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4377 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4377, [decl_e])))
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
              let uu____4419 = encode_term e1 env in
              match uu____4419 with
              | (ee1,decls1) ->
                  let uu____4426 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4426 with
                   | (xs,e21) ->
                       let uu____4440 = FStar_List.hd xs in
                       (match uu____4440 with
                        | (x1,uu____4448) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4450 = encode_body e21 env' in
                            (match uu____4450 with
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
            let uu____4472 =
              let uu____4476 =
                let uu____4477 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4477 in
              gen_term_var env uu____4476 in
            match uu____4472 with
            | (scrsym,scr',env1) ->
                let uu____4491 = encode_term e env1 in
                (match uu____4491 with
                 | (scr,decls) ->
                     let uu____4498 =
                       let encode_branch b uu____4514 =
                         match uu____4514 with
                         | (else_case,decls1) ->
                             let uu____4525 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4525 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4555  ->
                                       fun uu____4556  ->
                                         match (uu____4555, uu____4556) with
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
                                                       fun uu____4593  ->
                                                         match uu____4593
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4598 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4613 =
                                                     encode_term w1 env2 in
                                                   (match uu____4613 with
                                                    | (w2,decls21) ->
                                                        let uu____4621 =
                                                          let uu____4622 =
                                                            let uu____4625 =
                                                              let uu____4626
                                                                =
                                                                let uu____4629
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4629) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4626 in
                                                            (guard,
                                                              uu____4625) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4622 in
                                                        (uu____4621, decls21)) in
                                             (match uu____4598 with
                                              | (guard1,decls21) ->
                                                  let uu____4637 =
                                                    encode_br br env2 in
                                                  (match uu____4637 with
                                                   | (br1,decls3) ->
                                                       let uu____4645 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4645,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4498 with
                      | (match_tm,decls1) ->
                          let uu____4657 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4657, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4688 -> let uu____4689 = encode_one_pat env pat in [uu____4689]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4701 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4701
       then
         let uu____4702 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4702
       else ());
      (let uu____4704 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4704 with
       | (vars,pat_term) ->
           let uu____4714 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4737  ->
                     fun v1  ->
                       match uu____4737 with
                       | (env1,vars1) ->
                           let uu____4765 = gen_term_var env1 v1 in
                           (match uu____4765 with
                            | (xx,uu____4777,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4714 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4824 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4832 =
                        let uu____4835 = encode_const c in
                        (scrutinee, uu____4835) in
                      FStar_SMTEncoding_Util.mkEq uu____4832
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4854 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4854 with
                        | (uu____4858,uu____4859::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4861 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4882  ->
                                  match uu____4882 with
                                  | (arg,uu____4888) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4898 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4898)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4917 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4932 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4947 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4969  ->
                                  match uu____4969 with
                                  | (arg,uu____4978) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4988 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____4988)) in
                      FStar_All.pipe_right uu____4947 FStar_List.flatten in
                let pat_term1 uu____5004 = encode_term pat_term env1 in
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
      let uu____5011 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5026  ->
                fun uu____5027  ->
                  match (uu____5026, uu____5027) with
                  | ((tms,decls),(t,uu____5047)) ->
                      let uu____5058 = encode_term t env in
                      (match uu____5058 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5011 with | (l1,decls) -> ((FStar_List.rev l1), decls)
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
            let uu____5096 = FStar_Syntax_Util.list_elements e in
            match uu____5096 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 []) in
          let one_pat p =
            let uu____5114 =
              let uu____5124 = FStar_Syntax_Util.unmeta p in
              FStar_All.pipe_right uu____5124 FStar_Syntax_Util.head_and_args in
            match uu____5114 with
            | (head1,args) ->
                let uu____5155 =
                  let uu____5163 =
                    let uu____5164 = FStar_Syntax_Util.un_uinst head1 in
                    uu____5164.FStar_Syntax_Syntax.n in
                  (uu____5163, args) in
                (match uu____5155 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5178,uu____5179)::(e,uu____5181)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5212)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5233 -> failwith "Unexpected pattern term") in
          let lemma_pats p =
            let elts = list_elements1 p in
            let smt_pat_or t1 =
              let uu____5266 =
                let uu____5276 = FStar_Syntax_Util.unmeta t1 in
                FStar_All.pipe_right uu____5276
                  FStar_Syntax_Util.head_and_args in
              match uu____5266 with
              | (head1,args) ->
                  let uu____5305 =
                    let uu____5313 =
                      let uu____5314 = FStar_Syntax_Util.un_uinst head1 in
                      uu____5314.FStar_Syntax_Syntax.n in
                    (uu____5313, args) in
                  (match uu____5305 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5327)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5347 -> None) in
            match elts with
            | t1::[] ->
                let uu____5365 = smt_pat_or t1 in
                (match uu____5365 with
                 | Some e ->
                     let uu____5381 = list_elements1 e in
                     FStar_All.pipe_right uu____5381
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5398 = list_elements1 branch1 in
                             FStar_All.pipe_right uu____5398
                               (FStar_List.map one_pat)))
                 | uu____5412 ->
                     let uu____5416 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat) in
                     [uu____5416])
            | uu____5447 ->
                let uu____5449 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat) in
                [uu____5449] in
          let uu____5480 =
            let uu____5496 =
              let uu____5497 = FStar_Syntax_Subst.compress t in
              uu____5497.FStar_Syntax_Syntax.n in
            match uu____5496 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5527 = FStar_Syntax_Subst.open_comp binders c in
                (match uu____5527 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5562;
                            FStar_Syntax_Syntax.effect_name = uu____5563;
                            FStar_Syntax_Syntax.result_typ = uu____5564;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5566)::(post,uu____5568)::(pats,uu____5570)::[];
                            FStar_Syntax_Syntax.flags = uu____5571;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats in
                          let uu____5605 = lemma_pats pats' in
                          (binders1, pre, post, uu____5605)
                      | uu____5624 -> failwith "impos"))
            | uu____5640 -> failwith "Impos" in
          match uu____5480 with
          | (binders,pre,post,patterns) ->
              let uu____5684 = encode_binders None binders env in
              (match uu____5684 with
               | (vars,guards,env1,decls,uu____5699) ->
                   let uu____5706 =
                     let uu____5713 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5744 =
                                 let uu____5749 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5765  ->
                                           match uu____5765 with
                                           | (t1,uu____5772) ->
                                               encode_term t1
                                                 (let uu___146_5775 = env1 in
                                                  {
                                                    bindings =
                                                      (uu___146_5775.bindings);
                                                    depth =
                                                      (uu___146_5775.depth);
                                                    tcenv =
                                                      (uu___146_5775.tcenv);
                                                    warn =
                                                      (uu___146_5775.warn);
                                                    cache =
                                                      (uu___146_5775.cache);
                                                    nolabels =
                                                      (uu___146_5775.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___146_5775.encode_non_total_function_typ)
                                                  }))) in
                                 FStar_All.pipe_right uu____5749
                                   FStar_List.unzip in
                               match uu____5744 with
                               | (pats,decls1) -> (pats, decls1))) in
                     FStar_All.pipe_right uu____5713 FStar_List.unzip in
                   (match uu____5706 with
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
                                           let uu____5839 =
                                             let uu____5840 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5840 e in
                                           uu____5839 :: p))
                               | uu____5841 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5870 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e in
                                                 uu____5870 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5878 =
                                           let uu____5879 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort) in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5879 tl1 in
                                         aux uu____5878 vars2
                                     | uu____5880 -> pats in
                                   let uu____5884 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort) in
                                   aux uu____5884 vars) in
                        let env2 =
                          let uu___147_5886 = env1 in
                          {
                            bindings = (uu___147_5886.bindings);
                            depth = (uu___147_5886.depth);
                            tcenv = (uu___147_5886.tcenv);
                            warn = (uu___147_5886.warn);
                            cache = (uu___147_5886.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___147_5886.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___147_5886.encode_non_total_function_typ)
                          } in
                        let uu____5887 =
                          let uu____5890 = FStar_Syntax_Util.unmeta pre in
                          encode_formula uu____5890 env2 in
                        (match uu____5887 with
                         | (pre1,decls'') ->
                             let uu____5895 =
                               let uu____5898 = FStar_Syntax_Util.unmeta post in
                               encode_formula uu____5898 env2 in
                             (match uu____5895 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls''')) in
                                  let uu____5905 =
                                    let uu____5906 =
                                      let uu____5912 =
                                        let uu____5913 =
                                          let uu____5916 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards) in
                                          (uu____5916, post1) in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5913 in
                                      (pats1, vars, uu____5912) in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5906 in
                                  (uu____5905, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5929 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5929
        then
          let uu____5930 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5931 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5930 uu____5931
        else () in
      let enc f r l =
        let uu____5958 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5971 = encode_term (Prims.fst x) env in
                 match uu____5971 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5958 with
        | (decls,args) ->
            let uu____5988 =
              let uu___148_5989 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___148_5989.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___148_5989.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5988, decls) in
      let const_op f r uu____6008 = let uu____6011 = f r in (uu____6011, []) in
      let un_op f l =
        let uu____6027 = FStar_List.hd l in FStar_All.pipe_left f uu____6027 in
      let bin_op f uu___120_6040 =
        match uu___120_6040 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6048 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6075 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6084  ->
                 match uu____6084 with
                 | (t,uu____6092) ->
                     let uu____6093 = encode_formula t env in
                     (match uu____6093 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6075 with
        | (decls,phis) ->
            let uu____6110 =
              let uu___149_6111 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___149_6111.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___149_6111.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6110, decls) in
      let eq_op r uu___121_6127 =
        match uu___121_6127 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6187 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6187 r [e1; e2]
        | l ->
            let uu____6207 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6207 r l in
      let mk_imp1 r uu___122_6226 =
        match uu___122_6226 with
        | (lhs,uu____6230)::(rhs,uu____6232)::[] ->
            let uu____6253 = encode_formula rhs env in
            (match uu____6253 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6262) ->
                      (l1, decls1)
                  | uu____6265 ->
                      let uu____6266 = encode_formula lhs env in
                      (match uu____6266 with
                       | (l2,decls2) ->
                           let uu____6273 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6273, (FStar_List.append decls1 decls2)))))
        | uu____6275 -> failwith "impossible" in
      let mk_ite r uu___123_6290 =
        match uu___123_6290 with
        | (guard,uu____6294)::(_then,uu____6296)::(_else,uu____6298)::[] ->
            let uu____6327 = encode_formula guard env in
            (match uu____6327 with
             | (g,decls1) ->
                 let uu____6334 = encode_formula _then env in
                 (match uu____6334 with
                  | (t,decls2) ->
                      let uu____6341 = encode_formula _else env in
                      (match uu____6341 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6350 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6369 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6369 in
      let connectives =
        let uu____6381 =
          let uu____6390 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6390) in
        let uu____6403 =
          let uu____6413 =
            let uu____6422 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6422) in
          let uu____6435 =
            let uu____6445 =
              let uu____6455 =
                let uu____6464 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6464) in
              let uu____6477 =
                let uu____6487 =
                  let uu____6497 =
                    let uu____6506 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6506) in
                  [uu____6497;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6487 in
              uu____6455 :: uu____6477 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6445 in
          uu____6413 :: uu____6435 in
        uu____6381 :: uu____6403 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6668 = encode_formula phi' env in
            (match uu____6668 with
             | (phi2,decls) ->
                 let uu____6675 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6675, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6676 ->
            let uu____6681 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6681 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6710 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6710 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6718;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6720;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6736 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6736 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6768::(x,uu____6770)::(t,uu____6772)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6806 = encode_term x env in
                 (match uu____6806 with
                  | (x1,decls) ->
                      let uu____6813 = encode_term t env in
                      (match uu____6813 with
                       | (t1,decls') ->
                           let uu____6820 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6820, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6824)::(msg,uu____6826)::(phi2,uu____6828)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6862 =
                   let uu____6865 =
                     let uu____6866 = FStar_Syntax_Subst.compress r in
                     uu____6866.FStar_Syntax_Syntax.n in
                   let uu____6869 =
                     let uu____6870 = FStar_Syntax_Subst.compress msg in
                     uu____6870.FStar_Syntax_Syntax.n in
                   (uu____6865, uu____6869) in
                 (match uu____6862 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6877))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6893 -> fallback phi2)
             | uu____6896 when head_redex env head2 ->
                 let uu____6904 = whnf env phi1 in
                 encode_formula uu____6904 env
             | uu____6905 ->
                 let uu____6913 = encode_term phi1 env in
                 (match uu____6913 with
                  | (tt,decls) ->
                      let uu____6920 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___150_6921 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___150_6921.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___150_6921.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6920, decls)))
        | uu____6924 ->
            let uu____6925 = encode_term phi1 env in
            (match uu____6925 with
             | (tt,decls) ->
                 let uu____6932 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___151_6933 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___151_6933.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___151_6933.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6932, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6960 = encode_binders None bs env1 in
        match uu____6960 with
        | (vars,guards,env2,decls,uu____6982) ->
            let uu____6989 =
              let uu____6996 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7019 =
                          let uu____7024 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7038  ->
                                    match uu____7038 with
                                    | (t,uu____7044) ->
                                        encode_term t
                                          (let uu___152_7045 = env2 in
                                           {
                                             bindings =
                                               (uu___152_7045.bindings);
                                             depth = (uu___152_7045.depth);
                                             tcenv = (uu___152_7045.tcenv);
                                             warn = (uu___152_7045.warn);
                                             cache = (uu___152_7045.cache);
                                             nolabels =
                                               (uu___152_7045.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___152_7045.encode_non_total_function_typ)
                                           }))) in
                          FStar_All.pipe_right uu____7024 FStar_List.unzip in
                        match uu____7019 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____6996 FStar_List.unzip in
            (match uu____6989 with
             | (pats,decls') ->
                 let uu____7097 = encode_formula body env2 in
                 (match uu____7097 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7116;
                             FStar_SMTEncoding_Term.rng = uu____7117;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7125 -> guards in
                      let uu____7128 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7128, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7162  ->
                   match uu____7162 with
                   | (x,uu____7166) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7172 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7178 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7178) uu____7172 tl1 in
             let uu____7180 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7192  ->
                       match uu____7192 with
                       | (b,uu____7196) ->
                           let uu____7197 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7197)) in
             (match uu____7180 with
              | None  -> ()
              | Some (x,uu____7201) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7211 =
                    let uu____7212 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7212 in
                  FStar_Errors.warn pos uu____7211) in
       let uu____7213 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7213 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7219 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7255  ->
                     match uu____7255 with
                     | (l,uu____7265) -> FStar_Ident.lid_equals op l)) in
           (match uu____7219 with
            | None  -> fallback phi1
            | Some (uu____7288,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7317 = encode_q_body env vars pats body in
             match uu____7317 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7343 =
                     let uu____7349 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7349) in
                   FStar_SMTEncoding_Term.mkForall uu____7343
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7361 = encode_q_body env vars pats body in
             match uu____7361 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7386 =
                   let uu____7387 =
                     let uu____7393 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7393) in
                   FStar_SMTEncoding_Term.mkExists uu____7387
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7386, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7442 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7442 with
  | (asym,a) ->
      let uu____7447 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7447 with
       | (xsym,x) ->
           let uu____7452 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7452 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7482 =
                      let uu____7488 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7488, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7482 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7503 =
                      let uu____7507 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7507) in
                    FStar_SMTEncoding_Util.mkApp uu____7503 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7515 =
                    let uu____7517 =
                      let uu____7519 =
                        let uu____7521 =
                          let uu____7522 =
                            let uu____7527 =
                              let uu____7528 =
                                let uu____7534 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7534) in
                              FStar_SMTEncoding_Util.mkForall uu____7528 in
                            (uu____7527, None,
                              (Some (Prims.strcat "primitive_" x1))) in
                          FStar_SMTEncoding_Term.Assume uu____7522 in
                        let uu____7544 =
                          let uu____7546 =
                            let uu____7547 =
                              let uu____7552 =
                                let uu____7553 =
                                  let uu____7559 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7559) in
                                FStar_SMTEncoding_Util.mkForall uu____7553 in
                              (uu____7552,
                                (Some "Name-token correspondence"),
                                (Some
                                   (Prims.strcat "token_correspondence_" x1))) in
                            FStar_SMTEncoding_Term.Assume uu____7547 in
                          [uu____7546] in
                        uu____7521 :: uu____7544 in
                      xtok_decl :: uu____7519 in
                    xname_decl :: uu____7517 in
                  (xtok1, uu____7515) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7609 =
                    let uu____7617 =
                      let uu____7623 =
                        let uu____7624 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7624 in
                      quant axy uu____7623 in
                    (FStar_Syntax_Const.op_Eq, uu____7617) in
                  let uu____7630 =
                    let uu____7639 =
                      let uu____7647 =
                        let uu____7653 =
                          let uu____7654 =
                            let uu____7655 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7655 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7654 in
                        quant axy uu____7653 in
                      (FStar_Syntax_Const.op_notEq, uu____7647) in
                    let uu____7661 =
                      let uu____7670 =
                        let uu____7678 =
                          let uu____7684 =
                            let uu____7685 =
                              let uu____7686 =
                                let uu____7689 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7690 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7689, uu____7690) in
                              FStar_SMTEncoding_Util.mkLT uu____7686 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7685 in
                          quant xy uu____7684 in
                        (FStar_Syntax_Const.op_LT, uu____7678) in
                      let uu____7696 =
                        let uu____7705 =
                          let uu____7713 =
                            let uu____7719 =
                              let uu____7720 =
                                let uu____7721 =
                                  let uu____7724 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7725 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7724, uu____7725) in
                                FStar_SMTEncoding_Util.mkLTE uu____7721 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7720 in
                            quant xy uu____7719 in
                          (FStar_Syntax_Const.op_LTE, uu____7713) in
                        let uu____7731 =
                          let uu____7740 =
                            let uu____7748 =
                              let uu____7754 =
                                let uu____7755 =
                                  let uu____7756 =
                                    let uu____7759 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7760 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7759, uu____7760) in
                                  FStar_SMTEncoding_Util.mkGT uu____7756 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7755 in
                              quant xy uu____7754 in
                            (FStar_Syntax_Const.op_GT, uu____7748) in
                          let uu____7766 =
                            let uu____7775 =
                              let uu____7783 =
                                let uu____7789 =
                                  let uu____7790 =
                                    let uu____7791 =
                                      let uu____7794 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7795 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7794, uu____7795) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7791 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7790 in
                                quant xy uu____7789 in
                              (FStar_Syntax_Const.op_GTE, uu____7783) in
                            let uu____7801 =
                              let uu____7810 =
                                let uu____7818 =
                                  let uu____7824 =
                                    let uu____7825 =
                                      let uu____7826 =
                                        let uu____7829 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7830 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7829, uu____7830) in
                                      FStar_SMTEncoding_Util.mkSub uu____7826 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7825 in
                                  quant xy uu____7824 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7818) in
                              let uu____7836 =
                                let uu____7845 =
                                  let uu____7853 =
                                    let uu____7859 =
                                      let uu____7860 =
                                        let uu____7861 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7861 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7860 in
                                    quant qx uu____7859 in
                                  (FStar_Syntax_Const.op_Minus, uu____7853) in
                                let uu____7867 =
                                  let uu____7876 =
                                    let uu____7884 =
                                      let uu____7890 =
                                        let uu____7891 =
                                          let uu____7892 =
                                            let uu____7895 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7896 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7895, uu____7896) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7892 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7891 in
                                      quant xy uu____7890 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7884) in
                                  let uu____7902 =
                                    let uu____7911 =
                                      let uu____7919 =
                                        let uu____7925 =
                                          let uu____7926 =
                                            let uu____7927 =
                                              let uu____7930 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7931 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7930, uu____7931) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7927 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7926 in
                                        quant xy uu____7925 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7919) in
                                    let uu____7937 =
                                      let uu____7946 =
                                        let uu____7954 =
                                          let uu____7960 =
                                            let uu____7961 =
                                              let uu____7962 =
                                                let uu____7965 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7966 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7965, uu____7966) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7962 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7961 in
                                          quant xy uu____7960 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7954) in
                                      let uu____7972 =
                                        let uu____7981 =
                                          let uu____7989 =
                                            let uu____7995 =
                                              let uu____7996 =
                                                let uu____7997 =
                                                  let uu____8000 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8001 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8000, uu____8001) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____7997 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____7996 in
                                            quant xy uu____7995 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____7989) in
                                        let uu____8007 =
                                          let uu____8016 =
                                            let uu____8024 =
                                              let uu____8030 =
                                                let uu____8031 =
                                                  let uu____8032 =
                                                    let uu____8035 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8036 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8035, uu____8036) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8032 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8031 in
                                              quant xy uu____8030 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8024) in
                                          let uu____8042 =
                                            let uu____8051 =
                                              let uu____8059 =
                                                let uu____8065 =
                                                  let uu____8066 =
                                                    let uu____8067 =
                                                      let uu____8070 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8071 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8070,
                                                        uu____8071) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8067 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8066 in
                                                quant xy uu____8065 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8059) in
                                            let uu____8077 =
                                              let uu____8086 =
                                                let uu____8094 =
                                                  let uu____8100 =
                                                    let uu____8101 =
                                                      let uu____8102 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8102 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8101 in
                                                  quant qx uu____8100 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8094) in
                                              [uu____8086] in
                                            uu____8051 :: uu____8077 in
                                          uu____8016 :: uu____8042 in
                                        uu____7981 :: uu____8007 in
                                      uu____7946 :: uu____7972 in
                                    uu____7911 :: uu____7937 in
                                  uu____7876 :: uu____7902 in
                                uu____7845 :: uu____7867 in
                              uu____7810 :: uu____7836 in
                            uu____7775 :: uu____7801 in
                          uu____7740 :: uu____7766 in
                        uu____7705 :: uu____7731 in
                      uu____7670 :: uu____7696 in
                    uu____7639 :: uu____7661 in
                  uu____7609 :: uu____7630 in
                let mk1 l v1 =
                  let uu____8230 =
                    let uu____8235 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8267  ->
                              match uu____8267 with
                              | (l',uu____8276) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8235
                      (FStar_Option.map
                         (fun uu____8309  ->
                            match uu____8309 with | (uu____8320,b) -> b v1)) in
                  FStar_All.pipe_right uu____8230 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8361  ->
                          match uu____8361 with
                          | (l',uu____8370) -> FStar_Ident.lid_equals l l')) in
                { mk = mk1; is }))
let pretype_axiom:
  FStar_SMTEncoding_Term.term ->
    (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.decl
  =
  fun tapp  ->
    fun vars  ->
      let uu____8393 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      match uu____8393 with
      | (xxsym,xx) ->
          let uu____8398 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
          (match uu____8398 with
           | (ffsym,ff) ->
               let xx_has_type =
                 FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
               let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
               let uu____8405 =
                 let uu____8410 =
                   let uu____8411 =
                     let uu____8417 =
                       let uu____8418 =
                         let uu____8421 =
                           let uu____8422 =
                             let uu____8425 =
                               FStar_SMTEncoding_Util.mkApp ("PreType", [xx]) in
                             (tapp, uu____8425) in
                           FStar_SMTEncoding_Util.mkEq uu____8422 in
                         (xx_has_type, uu____8421) in
                       FStar_SMTEncoding_Util.mkImp uu____8418 in
                     ([[xx_has_type]],
                       ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                       (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                       uu____8417) in
                   FStar_SMTEncoding_Util.mkForall uu____8411 in
                 let uu____8438 =
                   let uu____8440 =
                     let uu____8441 =
                       let uu____8442 = FStar_Util.digest_of_string tapp_hash in
                       Prims.strcat "pretyping_" uu____8442 in
                     varops.mk_unique uu____8441 in
                   Some uu____8440 in
                 (uu____8410, (Some "pretyping"), uu____8438) in
               FStar_SMTEncoding_Term.Assume uu____8405)
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
    let uu____8473 =
      let uu____8474 =
        let uu____8479 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8479, (Some "unit typing"), (Some "unit_typing")) in
      FStar_SMTEncoding_Term.Assume uu____8474 in
    let uu____8482 =
      let uu____8484 =
        let uu____8485 =
          let uu____8490 =
            let uu____8491 =
              let uu____8497 =
                let uu____8498 =
                  let uu____8501 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8501) in
                FStar_SMTEncoding_Util.mkImp uu____8498 in
              ([[typing_pred]], [xx], uu____8497) in
            mkForall_fuel uu____8491 in
          (uu____8490, (Some "unit inversion"), (Some "unit_inversion")) in
        FStar_SMTEncoding_Term.Assume uu____8485 in
      [uu____8484] in
    uu____8473 :: uu____8482 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8530 =
      let uu____8531 =
        let uu____8536 =
          let uu____8537 =
            let uu____8543 =
              let uu____8546 =
                let uu____8548 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8548] in
              [uu____8546] in
            let uu____8551 =
              let uu____8552 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8552 tt in
            (uu____8543, [bb], uu____8551) in
          FStar_SMTEncoding_Util.mkForall uu____8537 in
        (uu____8536, (Some "bool typing"), (Some "bool_typing")) in
      FStar_SMTEncoding_Term.Assume uu____8531 in
    let uu____8564 =
      let uu____8566 =
        let uu____8567 =
          let uu____8572 =
            let uu____8573 =
              let uu____8579 =
                let uu____8580 =
                  let uu____8583 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8583) in
                FStar_SMTEncoding_Util.mkImp uu____8580 in
              ([[typing_pred]], [xx], uu____8579) in
            mkForall_fuel uu____8573 in
          (uu____8572, (Some "bool inversion"), (Some "bool_inversion")) in
        FStar_SMTEncoding_Term.Assume uu____8567 in
      [uu____8566] in
    uu____8530 :: uu____8564 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8618 =
        let uu____8619 =
          let uu____8623 =
            let uu____8625 =
              let uu____8627 =
                let uu____8629 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8630 =
                  let uu____8632 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8632] in
                uu____8629 :: uu____8630 in
              tt :: uu____8627 in
            tt :: uu____8625 in
          ("Prims.Precedes", uu____8623) in
        FStar_SMTEncoding_Util.mkApp uu____8619 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8618 in
    let precedes_y_x =
      let uu____8635 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8635 in
    let uu____8637 =
      let uu____8638 =
        let uu____8643 =
          let uu____8644 =
            let uu____8650 =
              let uu____8653 =
                let uu____8655 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8655] in
              [uu____8653] in
            let uu____8658 =
              let uu____8659 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8659 tt in
            (uu____8650, [bb], uu____8658) in
          FStar_SMTEncoding_Util.mkForall uu____8644 in
        (uu____8643, (Some "int typing"), (Some "int_typing")) in
      FStar_SMTEncoding_Term.Assume uu____8638 in
    let uu____8671 =
      let uu____8673 =
        let uu____8674 =
          let uu____8679 =
            let uu____8680 =
              let uu____8686 =
                let uu____8687 =
                  let uu____8690 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8690) in
                FStar_SMTEncoding_Util.mkImp uu____8687 in
              ([[typing_pred]], [xx], uu____8686) in
            mkForall_fuel uu____8680 in
          (uu____8679, (Some "int inversion"), (Some "int_inversion")) in
        FStar_SMTEncoding_Term.Assume uu____8674 in
      let uu____8704 =
        let uu____8706 =
          let uu____8707 =
            let uu____8712 =
              let uu____8713 =
                let uu____8719 =
                  let uu____8720 =
                    let uu____8723 =
                      let uu____8724 =
                        let uu____8726 =
                          let uu____8728 =
                            let uu____8730 =
                              let uu____8731 =
                                let uu____8734 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8735 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8734, uu____8735) in
                              FStar_SMTEncoding_Util.mkGT uu____8731 in
                            let uu____8736 =
                              let uu____8738 =
                                let uu____8739 =
                                  let uu____8742 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8743 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8742, uu____8743) in
                                FStar_SMTEncoding_Util.mkGTE uu____8739 in
                              let uu____8744 =
                                let uu____8746 =
                                  let uu____8747 =
                                    let uu____8750 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8751 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8750, uu____8751) in
                                  FStar_SMTEncoding_Util.mkLT uu____8747 in
                                [uu____8746] in
                              uu____8738 :: uu____8744 in
                            uu____8730 :: uu____8736 in
                          typing_pred_y :: uu____8728 in
                        typing_pred :: uu____8726 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8724 in
                    (uu____8723, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8720 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8719) in
              mkForall_fuel uu____8713 in
            (uu____8712, (Some "well-founded ordering on nat (alt)"),
              (Some "well-founded-ordering-on-nat")) in
          FStar_SMTEncoding_Term.Assume uu____8707 in
        [uu____8706] in
      uu____8673 :: uu____8704 in
    uu____8637 :: uu____8671 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8782 =
      let uu____8783 =
        let uu____8788 =
          let uu____8789 =
            let uu____8795 =
              let uu____8798 =
                let uu____8800 = FStar_SMTEncoding_Term.boxString b in
                [uu____8800] in
              [uu____8798] in
            let uu____8803 =
              let uu____8804 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8804 tt in
            (uu____8795, [bb], uu____8803) in
          FStar_SMTEncoding_Util.mkForall uu____8789 in
        (uu____8788, (Some "string typing"), (Some "string_typing")) in
      FStar_SMTEncoding_Term.Assume uu____8783 in
    let uu____8816 =
      let uu____8818 =
        let uu____8819 =
          let uu____8824 =
            let uu____8825 =
              let uu____8831 =
                let uu____8832 =
                  let uu____8835 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8835) in
                FStar_SMTEncoding_Util.mkImp uu____8832 in
              ([[typing_pred]], [xx], uu____8831) in
            mkForall_fuel uu____8825 in
          (uu____8824, (Some "string inversion"), (Some "string_inversion")) in
        FStar_SMTEncoding_Term.Assume uu____8819 in
      [uu____8818] in
    uu____8782 :: uu____8816 in
  let mk_ref1 env reft_name uu____8858 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8869 =
        let uu____8873 =
          let uu____8875 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8875] in
        (reft_name, uu____8873) in
      FStar_SMTEncoding_Util.mkApp uu____8869 in
    let refb =
      let uu____8878 =
        let uu____8882 =
          let uu____8884 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8884] in
        (reft_name, uu____8882) in
      FStar_SMTEncoding_Util.mkApp uu____8878 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8888 =
      let uu____8889 =
        let uu____8894 =
          let uu____8895 =
            let uu____8901 =
              let uu____8902 =
                let uu____8905 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8905) in
              FStar_SMTEncoding_Util.mkImp uu____8902 in
            ([[typing_pred]], [xx; aa], uu____8901) in
          mkForall_fuel uu____8895 in
        (uu____8894, (Some "ref inversion"), (Some "ref_inversion")) in
      FStar_SMTEncoding_Term.Assume uu____8889 in
    let uu____8921 =
      let uu____8923 =
        let uu____8924 =
          let uu____8929 =
            let uu____8930 =
              let uu____8936 =
                let uu____8937 =
                  let uu____8940 =
                    FStar_SMTEncoding_Util.mkAnd (typing_pred, typing_pred_b) in
                  let uu____8941 =
                    let uu____8942 =
                      let uu____8945 = FStar_SMTEncoding_Util.mkFreeV aa in
                      let uu____8946 = FStar_SMTEncoding_Util.mkFreeV bb in
                      (uu____8945, uu____8946) in
                    FStar_SMTEncoding_Util.mkEq uu____8942 in
                  (uu____8940, uu____8941) in
                FStar_SMTEncoding_Util.mkImp uu____8937 in
              ([[typing_pred; typing_pred_b]], [xx; aa; bb], uu____8936) in
            mkForall_fuel' (Prims.parse_int "2") uu____8930 in
          (uu____8929, (Some "ref typing is injective"),
            (Some "ref_injectivity")) in
        FStar_SMTEncoding_Term.Assume uu____8924 in
      [uu____8923] in
    uu____8888 :: uu____8921 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), (Some "true_interp"))] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8990 =
      let uu____8991 =
        let uu____8996 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8996, (Some "False interpretation"), (Some "false_interp")) in
      FStar_SMTEncoding_Term.Assume uu____8991 in
    [uu____8990] in
  let mk_and_interp env conj uu____9008 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9018 =
        let uu____9022 =
          let uu____9024 = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
          [uu____9024] in
        ("Valid", uu____9022) in
      FStar_SMTEncoding_Util.mkApp uu____9018 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9031 =
      let uu____9032 =
        let uu____9037 =
          let uu____9038 =
            let uu____9044 =
              let uu____9045 =
                let uu____9048 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9048, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9045 in
            ([[valid]], [aa; bb], uu____9044) in
          FStar_SMTEncoding_Util.mkForall uu____9038 in
        (uu____9037, (Some "/\\ interpretation"), (Some "l_and-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9032 in
    [uu____9031] in
  let mk_or_interp env disj uu____9073 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9083 =
        let uu____9087 =
          let uu____9089 = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
          [uu____9089] in
        ("Valid", uu____9087) in
      FStar_SMTEncoding_Util.mkApp uu____9083 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9096 =
      let uu____9097 =
        let uu____9102 =
          let uu____9103 =
            let uu____9109 =
              let uu____9110 =
                let uu____9113 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9113, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9110 in
            ([[valid]], [aa; bb], uu____9109) in
          FStar_SMTEncoding_Util.mkForall uu____9103 in
        (uu____9102, (Some "\\/ interpretation"), (Some "l_or-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9097 in
    [uu____9096] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let valid =
      let uu____9152 =
        let uu____9156 =
          let uu____9158 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
          [uu____9158] in
        ("Valid", uu____9156) in
      FStar_SMTEncoding_Util.mkApp uu____9152 in
    let uu____9161 =
      let uu____9162 =
        let uu____9167 =
          let uu____9168 =
            let uu____9174 =
              let uu____9175 =
                let uu____9178 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9178, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9175 in
            ([[valid]], [aa; xx1; yy1], uu____9174) in
          FStar_SMTEncoding_Util.mkForall uu____9168 in
        (uu____9167, (Some "Eq2 interpretation"), (Some "eq2-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9162 in
    [uu____9161] in
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
        let uu____9238 =
          let uu____9239 =
            let uu____9245 =
              let uu____9246 =
                let uu____9249 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9249, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9246 in
            ([[valid]], [aa; bb; xx1; yy1], uu____9245) in
          FStar_SMTEncoding_Util.mkForall uu____9239 in
        (uu____9238, (Some "Eq3 interpretation"), (Some "eq3-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9233 in
    [uu____9232] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9288 =
        let uu____9292 =
          let uu____9294 = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
          [uu____9294] in
        ("Valid", uu____9292) in
      FStar_SMTEncoding_Util.mkApp uu____9288 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9301 =
      let uu____9302 =
        let uu____9307 =
          let uu____9308 =
            let uu____9314 =
              let uu____9315 =
                let uu____9318 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9318, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9315 in
            ([[valid]], [aa; bb], uu____9314) in
          FStar_SMTEncoding_Util.mkForall uu____9308 in
        (uu____9307, (Some "==> interpretation"), (Some "l_imp-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9302 in
    [uu____9301] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9353 =
        let uu____9357 =
          let uu____9359 = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
          [uu____9359] in
        ("Valid", uu____9357) in
      FStar_SMTEncoding_Util.mkApp uu____9353 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9366 =
      let uu____9367 =
        let uu____9372 =
          let uu____9373 =
            let uu____9379 =
              let uu____9380 =
                let uu____9383 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9383, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9380 in
            ([[valid]], [aa; bb], uu____9379) in
          FStar_SMTEncoding_Util.mkForall uu____9373 in
        (uu____9372, (Some "<==> interpretation"), (Some "l_iff-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9367 in
    [uu____9366] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let valid =
      let uu____9414 =
        let uu____9418 =
          let uu____9420 = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
          [uu____9420] in
        ("Valid", uu____9418) in
      FStar_SMTEncoding_Util.mkApp uu____9414 in
    let not_valid_a =
      let uu____9424 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9424 in
    let uu____9426 =
      let uu____9427 =
        let uu____9432 =
          let uu____9433 =
            let uu____9439 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[valid]], [aa], uu____9439) in
          FStar_SMTEncoding_Util.mkForall uu____9433 in
        (uu____9432, (Some "not interpretation"), (Some "l_not-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9427 in
    [uu____9426] in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let valid =
      let uu____9476 =
        let uu____9480 =
          let uu____9482 = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b]) in
          [uu____9482] in
        ("Valid", uu____9480) in
      FStar_SMTEncoding_Util.mkApp uu____9476 in
    let valid_b_x =
      let uu____9486 =
        let uu____9490 =
          let uu____9492 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9492] in
        ("Valid", uu____9490) in
      FStar_SMTEncoding_Util.mkApp uu____9486 in
    let uu____9494 =
      let uu____9495 =
        let uu____9500 =
          let uu____9501 =
            let uu____9507 =
              let uu____9508 =
                let uu____9511 =
                  let uu____9512 =
                    let uu____9518 =
                      let uu____9521 =
                        let uu____9523 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9523] in
                      [uu____9521] in
                    let uu____9526 =
                      let uu____9527 =
                        let uu____9530 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9530, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9527 in
                    (uu____9518, [xx1], uu____9526) in
                  FStar_SMTEncoding_Util.mkForall uu____9512 in
                (uu____9511, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9508 in
            ([[valid]], [aa; bb], uu____9507) in
          FStar_SMTEncoding_Util.mkForall uu____9501 in
        (uu____9500, (Some "forall interpretation"), (Some "forall-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9495 in
    [uu____9494] in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let valid =
      let uu____9578 =
        let uu____9582 =
          let uu____9584 = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b]) in
          [uu____9584] in
        ("Valid", uu____9582) in
      FStar_SMTEncoding_Util.mkApp uu____9578 in
    let valid_b_x =
      let uu____9588 =
        let uu____9592 =
          let uu____9594 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9594] in
        ("Valid", uu____9592) in
      FStar_SMTEncoding_Util.mkApp uu____9588 in
    let uu____9596 =
      let uu____9597 =
        let uu____9602 =
          let uu____9603 =
            let uu____9609 =
              let uu____9610 =
                let uu____9613 =
                  let uu____9614 =
                    let uu____9620 =
                      let uu____9623 =
                        let uu____9625 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9625] in
                      [uu____9623] in
                    let uu____9628 =
                      let uu____9629 =
                        let uu____9632 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9632, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9629 in
                    (uu____9620, [xx1], uu____9628) in
                  FStar_SMTEncoding_Util.mkExists uu____9614 in
                (uu____9613, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9610 in
            ([[valid]], [aa; bb], uu____9609) in
          FStar_SMTEncoding_Util.mkForall uu____9603 in
        (uu____9602, (Some "exists interpretation"), (Some "exists-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9597 in
    [uu____9596] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9669 =
      let uu____9670 =
        let uu____9675 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9676 =
          let uu____9678 = varops.mk_unique "typing_range_const" in
          Some uu____9678 in
        (uu____9675, (Some "Range_const typing"), uu____9676) in
      FStar_SMTEncoding_Term.Assume uu____9670 in
    [uu____9669] in
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
          let uu____9941 =
            FStar_Util.find_opt
              (fun uu____9959  ->
                 match uu____9959 with
                 | (l,uu____9969) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9941 with
          | None  -> []
          | Some (uu____9991,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10028 = encode_function_type_as_formula None None t env in
        match uu____10028 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Term.Assume
                 (form, (Some (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Some (Prims.strcat "lemma_" lid.FStar_Ident.str)))]
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
            let uu____10061 =
              (let uu____10062 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10062) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10061
            then
              let uu____10066 = new_term_constant_and_tok_from_lid env lid in
              match uu____10066 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10078 =
                      let uu____10079 = FStar_Syntax_Subst.compress t_norm in
                      uu____10079.FStar_Syntax_Syntax.n in
                    match uu____10078 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10084) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10101  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10104 -> [] in
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
              (let uu____10113 = prims.is lid in
               if uu____10113
               then
                 let vname = varops.new_fvar lid in
                 let uu____10118 = prims.mk lid vname in
                 match uu____10118 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10133 =
                    let uu____10139 = curried_arrow_formals_comp t_norm in
                    match uu____10139 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10150 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10150
                          then
                            let uu____10151 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___153_10152 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___153_10152.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___153_10152.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___153_10152.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___153_10152.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___153_10152.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___153_10152.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___153_10152.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___153_10152.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___153_10152.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___153_10152.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___153_10152.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___153_10152.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___153_10152.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___153_10152.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___153_10152.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___153_10152.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___153_10152.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___153_10152.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___153_10152.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___153_10152.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___153_10152.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___153_10152.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___153_10152.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10151
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10159 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10159)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10133 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10186 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10186 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10199 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___124_10223  ->
                                     match uu___124_10223 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10226 =
                                           FStar_Util.prefix vars in
                                         (match uu____10226 with
                                          | (uu____10237,(xxsym,uu____10239))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10249 =
                                                let uu____10250 =
                                                  let uu____10255 =
                                                    let uu____10256 =
                                                      let uu____10262 =
                                                        let uu____10263 =
                                                          let uu____10266 =
                                                            let uu____10267 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10267 in
                                                          (vapp, uu____10266) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10263 in
                                                      ([[vapp]], vars,
                                                        uu____10262) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10256 in
                                                  (uu____10255,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Some
                                                       (Prims.strcat
                                                          "disc_equation_"
                                                          (escape
                                                             d.FStar_Ident.str)))) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10250 in
                                              [uu____10249])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10279 =
                                           FStar_Util.prefix vars in
                                         (match uu____10279 with
                                          | (uu____10290,(xxsym,uu____10292))
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
                                              let uu____10306 =
                                                let uu____10307 =
                                                  let uu____10312 =
                                                    let uu____10313 =
                                                      let uu____10319 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10319) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10313 in
                                                  (uu____10312,
                                                    (Some
                                                       "Projector equation"),
                                                    (Some
                                                       (Prims.strcat
                                                          "proj_equation_"
                                                          tp_name))) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10307 in
                                              [uu____10306])
                                     | uu____10329 -> [])) in
                           let uu____10330 = encode_binders None formals env1 in
                           (match uu____10330 with
                            | (vars,guards,env',decls1,uu____10346) ->
                                let uu____10353 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10358 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10358, decls1)
                                  | Some p ->
                                      let uu____10360 = encode_formula p env' in
                                      (match uu____10360 with
                                       | (g,ds) ->
                                           let uu____10367 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10367,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10353 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10376 =
                                         let uu____10380 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10380) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10376 in
                                     let uu____10385 =
                                       let vname_decl =
                                         let uu____10390 =
                                           let uu____10396 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10401  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10396,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10390 in
                                       let uu____10406 =
                                         let env2 =
                                           let uu___154_10410 = env1 in
                                           {
                                             bindings =
                                               (uu___154_10410.bindings);
                                             depth = (uu___154_10410.depth);
                                             tcenv = (uu___154_10410.tcenv);
                                             warn = (uu___154_10410.warn);
                                             cache = (uu___154_10410.cache);
                                             nolabels =
                                               (uu___154_10410.nolabels);
                                             use_zfuel_name =
                                               (uu___154_10410.use_zfuel_name);
                                             encode_non_total_function_typ
                                           } in
                                         let uu____10411 =
                                           let uu____10412 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10412 in
                                         if uu____10411
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10406 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             FStar_SMTEncoding_Term.Assume
                                               (tok_typing,
                                                 (Some
                                                    "function token typing"),
                                                 (Some
                                                    (Prims.strcat
                                                       "function_token_typing_"
                                                       vname))) in
                                           let uu____10424 =
                                             match formals with
                                             | [] ->
                                                 let uu____10433 =
                                                   let uu____10434 =
                                                     let uu____10436 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10436 in
                                                   push_free_var env1 lid
                                                     vname uu____10434 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10433)
                                             | uu____10439 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10444 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10444 in
                                                 let name_tok_corr =
                                                   let uu____10446 =
                                                     let uu____10451 =
                                                       let uu____10452 =
                                                         let uu____10458 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10458) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10452 in
                                                     (uu____10451,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Some
                                                          (Prims.strcat
                                                             "token_correspondence_"
                                                             vname))) in
                                                   FStar_SMTEncoding_Term.Assume
                                                     uu____10446 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10424 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10385 with
                                      | (decls2,env2) ->
                                          let uu____10483 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10488 =
                                              encode_term res_t1 env' in
                                            match uu____10488 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10496 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10496,
                                                  decls) in
                                          (match uu____10483 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10504 =
                                                   let uu____10509 =
                                                     let uu____10510 =
                                                       let uu____10516 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10516) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10510 in
                                                   (uu____10509,
                                                     (Some "free var typing"),
                                                     (Some
                                                        (Prims.strcat
                                                           "typing_" vname))) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____10504 in
                                               let freshness =
                                                 let uu____10526 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10526
                                                 then
                                                   let uu____10529 =
                                                     let uu____10530 =
                                                       let uu____10536 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10542 =
                                                         varops.next_id () in
                                                       (vname, uu____10536,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10542) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10530 in
                                                   let uu____10544 =
                                                     let uu____10546 =
                                                       pretype_axiom vapp
                                                         vars in
                                                     [uu____10546] in
                                                   uu____10529 :: uu____10544
                                                 else [] in
                                               let g =
                                                 let uu____10550 =
                                                   let uu____10552 =
                                                     let uu____10554 =
                                                       let uu____10556 =
                                                         let uu____10558 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10558 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10556 in
                                                     FStar_List.append decls3
                                                       uu____10554 in
                                                   FStar_List.append decls2
                                                     uu____10552 in
                                                 FStar_List.append decls11
                                                   uu____10550 in
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
          let uu____10580 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10580 with
          | None  ->
              let uu____10603 = encode_free_var env x t t_norm [] in
              (match uu____10603 with
               | (decls,env1) ->
                   let uu____10618 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10618 with
                    | (n1,x',uu____10637) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10649) -> ((n1, x1), [], env)
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
          let uu____10682 = encode_free_var env lid t tt quals in
          match uu____10682 with
          | (decls,env1) ->
              let uu____10693 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10693
              then
                let uu____10697 =
                  let uu____10699 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10699 in
                (uu____10697, env1)
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
             (fun uu____10727  ->
                fun lb  ->
                  match uu____10727 with
                  | (decls,env1) ->
                      let uu____10739 =
                        let uu____10743 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10743
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10739 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10767  ->
      fun quals  ->
        match uu____10767 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10816 = FStar_Util.first_N nbinders formals in
              match uu____10816 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10856  ->
                         fun uu____10857  ->
                           match (uu____10856, uu____10857) with
                           | ((formal,uu____10867),(binder,uu____10869)) ->
                               let uu____10874 =
                                 let uu____10879 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10879) in
                               FStar_Syntax_Syntax.NT uu____10874) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10884 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10898  ->
                              match uu____10898 with
                              | (x,i) ->
                                  let uu____10905 =
                                    let uu___155_10906 = x in
                                    let uu____10907 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___155_10906.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___155_10906.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10907
                                    } in
                                  (uu____10905, i))) in
                    FStar_All.pipe_right uu____10884
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10919 =
                      let uu____10921 =
                        let uu____10922 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10922.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10921 in
                    let uu____10926 =
                      let uu____10927 = FStar_Syntax_Subst.compress body in
                      let uu____10928 =
                        let uu____10929 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10929 in
                      FStar_Syntax_Syntax.extend_app_n uu____10927
                        uu____10928 in
                    uu____10926 uu____10919 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10971 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10971
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___156_10972 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___156_10972.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___156_10972.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___156_10972.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___156_10972.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___156_10972.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___156_10972.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___156_10972.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___156_10972.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___156_10972.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___156_10972.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___156_10972.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___156_10972.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___156_10972.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___156_10972.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___156_10972.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___156_10972.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___156_10972.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___156_10972.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___156_10972.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___156_10972.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___156_10972.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___156_10972.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___156_10972.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____10993 = FStar_Syntax_Util.abs_formals e in
                match uu____10993 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11042::uu____11043 ->
                         let uu____11051 =
                           let uu____11052 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11052.FStar_Syntax_Syntax.n in
                         (match uu____11051 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11079 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11079 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11105 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11105
                                   then
                                     let uu____11123 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11123 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11169  ->
                                                   fun uu____11170  ->
                                                     match (uu____11169,
                                                             uu____11170)
                                                     with
                                                     | ((x,uu____11180),
                                                        (b,uu____11182)) ->
                                                         let uu____11187 =
                                                           let uu____11192 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11192) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11187)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11194 =
                                            let uu____11205 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11205) in
                                          (uu____11194, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11240 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11240 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11292) ->
                              let uu____11297 =
                                let uu____11308 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11308 in
                              (uu____11297, true)
                          | uu____11341 when Prims.op_Negation norm1 ->
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
                          | uu____11343 ->
                              let uu____11344 =
                                let uu____11345 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11346 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11345
                                  uu____11346 in
                              failwith uu____11344)
                     | uu____11359 ->
                         let uu____11360 =
                           let uu____11361 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11361.FStar_Syntax_Syntax.n in
                         (match uu____11360 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11388 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11388 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11406 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11406 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11454 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11482 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         FStar_Syntax_Util.is_lemma
                           lb.FStar_Syntax_Syntax.lbtyp)) in
               if uu____11482
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11489 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11530  ->
                            fun lb  ->
                              match uu____11530 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11581 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11581
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11584 =
                                      let uu____11592 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11592
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11584 with
                                    | (tok,decl,env2) ->
                                        let uu____11617 =
                                          let uu____11624 =
                                            let uu____11630 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11630, tok) in
                                          uu____11624 :: toks in
                                        (uu____11617, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11489 with
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
                        | uu____11732 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11737 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11737 vars)
                            else
                              (let uu____11739 =
                                 let uu____11743 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11743) in
                               FStar_SMTEncoding_Util.mkApp uu____11739) in
                      let uu____11748 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___125_11750  ->
                                 match uu___125_11750 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11751 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11754 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11754))) in
                      if uu____11748
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11774;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11776;
                                FStar_Syntax_Syntax.lbeff = uu____11777;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11818 =
                                 FStar_Syntax_Subst.univ_var_opening uvs in
                               (match uu____11818 with
                                | (univ_subst,univ_vars1) ->
                                    let env' =
                                      let uu___159_11833 = env1 in
                                      let uu____11834 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1.tcenv univ_vars1 in
                                      {
                                        bindings = (uu___159_11833.bindings);
                                        depth = (uu___159_11833.depth);
                                        tcenv = uu____11834;
                                        warn = (uu___159_11833.warn);
                                        cache = (uu___159_11833.cache);
                                        nolabels = (uu___159_11833.nolabels);
                                        use_zfuel_name =
                                          (uu___159_11833.use_zfuel_name);
                                        encode_non_total_function_typ =
                                          (uu___159_11833.encode_non_total_function_typ)
                                      } in
                                    let t_norm1 =
                                      FStar_Syntax_Subst.subst univ_subst
                                        t_norm in
                                    let e1 =
                                      let uu____11837 =
                                        FStar_Syntax_Subst.subst univ_subst e in
                                      FStar_Syntax_Subst.compress uu____11837 in
                                    let uu____11838 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11838 with
                                     | ((binders,body,uu____11850,uu____11851),curry)
                                         ->
                                         ((let uu____11858 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11858
                                           then
                                             let uu____11859 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11860 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11859 uu____11860
                                           else ());
                                          (let uu____11862 =
                                             encode_binders None binders env' in
                                           match uu____11862 with
                                           | (vars,guards,env'1,binder_decls,uu____11878)
                                               ->
                                               let body1 =
                                                 let uu____11886 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11886
                                                 then
                                                   reify_body env'1.tcenv
                                                     body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11889 =
                                                 let uu____11894 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11894
                                                 then
                                                   let uu____11900 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11901 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11900, uu____11901)
                                                 else
                                                   (let uu____11907 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11907)) in
                                               (match uu____11889 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11921 =
                                                        let uu____11926 =
                                                          let uu____11927 =
                                                            let uu____11933 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11933) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11927 in
                                                        let uu____11939 =
                                                          let uu____11941 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11941 in
                                                        (uu____11926,
                                                          uu____11939,
                                                          (Some
                                                             (Prims.strcat
                                                                "equation_" f))) in
                                                      FStar_SMTEncoding_Term.Assume
                                                        uu____11921 in
                                                    let uu____11944 =
                                                      let uu____11946 =
                                                        let uu____11948 =
                                                          let uu____11950 =
                                                            let uu____11952 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11952 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11950 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11948 in
                                                      FStar_List.append
                                                        decls1 uu____11946 in
                                                    (uu____11944, env1))))))
                           | uu____11955 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11974 = varops.fresh "fuel" in
                             (uu____11974, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____11977 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12016  ->
                                     fun uu____12017  ->
                                       match (uu____12016, uu____12017) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12099 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12099 in
                                           let gtok =
                                             let uu____12101 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12101 in
                                           let env3 =
                                             let uu____12103 =
                                               let uu____12105 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12105 in
                                             push_free_var env2 flid gtok
                                               uu____12103 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____11977 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12189
                                 t_norm uu____12191 =
                                 match (uu____12189, uu____12191) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12216;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12217;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12234 =
                                       FStar_Syntax_Subst.univ_var_opening
                                         uvs in
                                     (match uu____12234 with
                                      | (univ_subst,univ_vars1) ->
                                          let env' =
                                            let uu___160_12251 = env2 in
                                            let uu____12252 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env2.tcenv univ_vars1 in
                                            {
                                              bindings =
                                                (uu___160_12251.bindings);
                                              depth = (uu___160_12251.depth);
                                              tcenv = uu____12252;
                                              warn = (uu___160_12251.warn);
                                              cache = (uu___160_12251.cache);
                                              nolabels =
                                                (uu___160_12251.nolabels);
                                              use_zfuel_name =
                                                (uu___160_12251.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___160_12251.encode_non_total_function_typ)
                                            } in
                                          let t_norm1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst t_norm in
                                          let e1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst e in
                                          ((let uu____12256 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12256
                                            then
                                              let uu____12257 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12258 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12259 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12257 uu____12258
                                                uu____12259
                                            else ());
                                           (let uu____12261 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12261 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12283 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12283
                                                  then
                                                    let uu____12284 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12285 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12286 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12287 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12284 uu____12285
                                                      uu____12286 uu____12287
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12291 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12291 with
                                                  | (vars,guards,env'1,binder_decls,uu____12309)
                                                      ->
                                                      let decl_g =
                                                        let uu____12317 =
                                                          let uu____12323 =
                                                            let uu____12325 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12325 in
                                                          (g, uu____12323,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12317 in
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
                                                        let uu____12340 =
                                                          let uu____12344 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12344) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12340 in
                                                      let gsapp =
                                                        let uu____12350 =
                                                          let uu____12354 =
                                                            let uu____12356 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12356 ::
                                                              vars_tm in
                                                          (g, uu____12354) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12350 in
                                                      let gmax =
                                                        let uu____12360 =
                                                          let uu____12364 =
                                                            let uu____12366 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12366 ::
                                                              vars_tm in
                                                          (g, uu____12364) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12360 in
                                                      let body1 =
                                                        let uu____12370 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12370
                                                        then
                                                          reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12372 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12372 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12383
                                                               =
                                                               let uu____12388
                                                                 =
                                                                 let uu____12389
                                                                   =
                                                                   let uu____12397
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
                                                                    uu____12397) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12389 in
                                                               let uu____12408
                                                                 =
                                                                 let uu____12410
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12410 in
                                                               (uu____12388,
                                                                 uu____12408,
                                                                 (Some
                                                                    (
                                                                    Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12383 in
                                                           let eqn_f =
                                                             let uu____12414
                                                               =
                                                               let uu____12419
                                                                 =
                                                                 let uu____12420
                                                                   =
                                                                   let uu____12426
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12426) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12420 in
                                                               (uu____12419,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Some
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g))) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12414 in
                                                           let eqn_g' =
                                                             let uu____12435
                                                               =
                                                               let uu____12440
                                                                 =
                                                                 let uu____12441
                                                                   =
                                                                   let uu____12447
                                                                    =
                                                                    let uu____12448
                                                                    =
                                                                    let uu____12451
                                                                    =
                                                                    let uu____12452
                                                                    =
                                                                    let uu____12456
                                                                    =
                                                                    let uu____12458
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12458
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12456) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12452 in
                                                                    (gsapp,
                                                                    uu____12451) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12448 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12447) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12441 in
                                                               (uu____12440,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Some
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g))) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12435 in
                                                           let uu____12471 =
                                                             let uu____12476
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12476
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12493)
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
                                                                    let uu____12508
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12508
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12511
                                                                    =
                                                                    let uu____12516
                                                                    =
                                                                    let uu____12517
                                                                    =
                                                                    let uu____12523
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12523) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12517 in
                                                                    (uu____12516,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))) in
                                                                   FStar_SMTEncoding_Term.Assume
                                                                    uu____12511 in
                                                                 let uu____12535
                                                                   =
                                                                   let uu____12539
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12539
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12547
                                                                    =
                                                                    let uu____12549
                                                                    =
                                                                    let uu____12550
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
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12566,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12563 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12562) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12556 in
                                                                    (uu____12555,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12550 in
                                                                    [uu____12549] in
                                                                    (d3,
                                                                    uu____12547) in
                                                                 (match uu____12535
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12471
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
                               let uu____12602 =
                                 let uu____12609 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12641  ->
                                      fun uu____12642  ->
                                        match (uu____12641, uu____12642) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12718 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12718 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12609 in
                               (match uu____12602 with
                                | (decls2,eqns,env01) ->
                                    let uu____12758 =
                                      let isDeclFun uu___126_12766 =
                                        match uu___126_12766 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12767 -> true
                                        | uu____12773 -> false in
                                      let uu____12774 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12774
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12758 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12801 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12801
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
      (let uu____12834 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____12834
       then
         let uu____12835 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
           uu____12835
       else ());
      (let nm =
         let uu____12838 = FStar_Syntax_Util.lid_of_sigelt se in
         match uu____12838 with | None  -> "" | Some l -> l.FStar_Ident.str in
       let uu____12841 = encode_sigelt' env se in
       match uu____12841 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12850 =
                  let uu____12852 =
                    let uu____12853 = FStar_Util.format1 "<Skipped %s/>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12853 in
                  [uu____12852] in
                (uu____12850, e)
            | uu____12855 ->
                let uu____12856 =
                  let uu____12858 =
                    let uu____12860 =
                      let uu____12861 =
                        FStar_Util.format1 "<Start encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12861 in
                    uu____12860 :: g in
                  let uu____12862 =
                    let uu____12864 =
                      let uu____12865 =
                        FStar_Util.format1 "</end encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12865 in
                    [uu____12864] in
                  FStar_List.append uu____12858 uu____12862 in
                (uu____12856, e)))
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12873 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect (ed,uu____12884) ->
          let uu____12885 =
            let uu____12886 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12886 Prims.op_Negation in
          if uu____12885
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12906 ->
                   let uu____12907 =
                     let uu____12910 =
                       let uu____12911 =
                         let uu____12926 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12926) in
                       FStar_Syntax_Syntax.Tm_abs uu____12911 in
                     FStar_Syntax_Syntax.mk uu____12910 in
                   uu____12907 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____12979 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____12979 with
               | (aname,atok,env2) ->
                   let uu____12989 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____12989 with
                    | (formals,uu____12999) ->
                        let uu____13006 =
                          let uu____13009 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13009 env2 in
                        (match uu____13006 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13017 =
                                 let uu____13018 =
                                   let uu____13024 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13032  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13024,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13018 in
                               [uu____13017;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13039 =
                               let aux uu____13068 uu____13069 =
                                 match (uu____13068, uu____13069) with
                                 | ((bv,uu____13096),(env3,acc_sorts,acc)) ->
                                     let uu____13117 = gen_term_var env3 bv in
                                     (match uu____13117 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13039 with
                              | (uu____13155,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13169 =
                                      let uu____13174 =
                                        let uu____13175 =
                                          let uu____13181 =
                                            let uu____13182 =
                                              let uu____13185 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13185) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13182 in
                                          ([[app]], xs_sorts, uu____13181) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13175 in
                                      (uu____13174, (Some "Action equality"),
                                        (Some
                                           (Prims.strcat aname "_equality"))) in
                                    FStar_SMTEncoding_Term.Assume uu____13169 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13198 =
                                      let uu____13203 =
                                        let uu____13204 =
                                          let uu____13210 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13210) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13204 in
                                      (uu____13203,
                                        (Some "Action token correspondence"),
                                        (Some
                                           (Prims.strcat aname
                                              "_token_correspondence"))) in
                                    FStar_SMTEncoding_Term.Assume uu____13198 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13221 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13221 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____13237,uu____13238,uu____13239,uu____13240) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13243 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13243 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____13254,t,quals,uu____13257) ->
          let will_encode_definition =
            let uu____13261 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___127_13263  ->
                      match uu___127_13263 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13266 -> false)) in
            Prims.op_Negation uu____13261 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13272 = encode_top_level_val env fv t quals in
             match uu____13272 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13284 =
                   let uu____13286 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13286 in
                 (uu____13284, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____13291,uu____13292) ->
          let uu____13295 = encode_formula f env in
          (match uu____13295 with
           | (f1,decls) ->
               let g =
                 let uu____13304 =
                   let uu____13305 =
                     let uu____13310 =
                       let uu____13312 =
                         let uu____13313 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13313 in
                       Some uu____13312 in
                     let uu____13314 =
                       let uu____13316 =
                         varops.mk_unique
                           (Prims.strcat "assumption_" l.FStar_Ident.str) in
                       Some uu____13316 in
                     (f1, uu____13310, uu____13314) in
                   FStar_SMTEncoding_Term.Assume uu____13305 in
                 [uu____13304] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,r,uu____13322,quals,uu____13324)
          when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13332 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13339 =
                       let uu____13344 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13344.FStar_Syntax_Syntax.fv_name in
                     uu____13339.FStar_Syntax_Syntax.v in
                   let uu____13348 =
                     let uu____13349 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13349 in
                   if uu____13348
                   then
                     let val_decl =
                       FStar_Syntax_Syntax.Sig_declare_typ
                         (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp), quals, r) in
                     let uu____13368 = encode_sigelt' env1 val_decl in
                     match uu____13368 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13332 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13385,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13387;
                          FStar_Syntax_Syntax.lbtyp = uu____13388;
                          FStar_Syntax_Syntax.lbeff = uu____13389;
                          FStar_Syntax_Syntax.lbdef = uu____13390;_}::[]),uu____13391,uu____13392,uu____13393,uu____13394)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13410 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13410 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let valid_b2t_x =
                 let uu____13428 =
                   let uu____13432 =
                     let uu____13434 =
                       FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
                     [uu____13434] in
                   ("Valid", uu____13432) in
                 FStar_SMTEncoding_Util.mkApp uu____13428 in
               let decls =
                 let uu____13439 =
                   let uu____13441 =
                     let uu____13442 =
                       let uu____13447 =
                         let uu____13448 =
                           let uu____13454 =
                             let uu____13455 =
                               let uu____13458 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13458) in
                             FStar_SMTEncoding_Util.mkEq uu____13455 in
                           ([[valid_b2t_x]], [xx], uu____13454) in
                         FStar_SMTEncoding_Util.mkForall uu____13448 in
                       (uu____13447, (Some "b2t def"), (Some "b2t_def")) in
                     FStar_SMTEncoding_Term.Assume uu____13442 in
                   [uu____13441] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13439 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let
          (uu____13476,uu____13477,uu____13478,quals,uu____13480) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___128_13488  ->
                  match uu___128_13488 with
                  | FStar_Syntax_Syntax.Discriminator uu____13489 -> true
                  | uu____13490 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          (uu____13492,uu____13493,lids,quals,uu____13496) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13505 =
                     let uu____13506 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13506.FStar_Ident.idText in
                   uu____13505 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___129_13508  ->
                     match uu___129_13508 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13509 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13512,uu____13513,quals,uu____13515) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___130_13527  ->
                  match uu___130_13527 with
                  | FStar_Syntax_Syntax.Projector uu____13528 -> true
                  | uu____13531 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13538 = try_lookup_free_var env l in
          (match uu____13538 with
           | Some uu____13542 -> ([], env)
           | None  ->
               let se1 =
                 FStar_Syntax_Syntax.Sig_declare_typ
                   (l, (lb.FStar_Syntax_Syntax.lbunivs),
                     (lb.FStar_Syntax_Syntax.lbtyp), quals,
                     (FStar_Ident.range_of_lid l)) in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13551,uu____13552,quals,uu____13554) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle
          (ses,uu____13568,uu____13569,uu____13570) ->
          let uu____13577 = encode_signature env ses in
          (match uu____13577 with
           | (g,env1) ->
               let uu____13587 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___131_13597  ->
                         match uu___131_13597 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13598,Some "inversion axiom",uu____13599)
                             -> false
                         | uu____13603 -> true)) in
               (match uu____13587 with
                | (g',inversions) ->
                    let uu____13612 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___132_13622  ->
                              match uu___132_13622 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13623 ->
                                  true
                              | uu____13629 -> false)) in
                    (match uu____13612 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13640,tps,k,uu____13643,datas,quals,uu____13646) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___133_13655  ->
                    match uu___133_13655 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13656 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13663 = c in
              match uu____13663 with
              | (name,args,uu____13667,uu____13668,uu____13669) ->
                  let uu____13672 =
                    let uu____13673 =
                      let uu____13679 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13686  ->
                                match uu____13686 with
                                | (uu____13690,sort,uu____13692) -> sort)) in
                      (name, uu____13679, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13673 in
                  [uu____13672]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13710 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13713 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13713 FStar_Option.isNone)) in
            if uu____13710
            then []
            else
              (let uu____13730 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13730 with
               | (xxsym,xx) ->
                   let uu____13736 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13747  ->
                             fun l  ->
                               match uu____13747 with
                               | (out,decls) ->
                                   let uu____13759 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13759 with
                                    | (uu____13765,data_t) ->
                                        let uu____13767 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13767 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13796 =
                                                 let uu____13797 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13797.FStar_Syntax_Syntax.n in
                                               match uu____13796 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13805,indices) ->
                                                   indices
                                               | uu____13821 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13833  ->
                                                         match uu____13833
                                                         with
                                                         | (x,uu____13837) ->
                                                             let uu____13838
                                                               =
                                                               let uu____13839
                                                                 =
                                                                 let uu____13843
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13843,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13839 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13838)
                                                    env) in
                                             let uu____13845 =
                                               encode_args indices env1 in
                                             (match uu____13845 with
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
                                                      let uu____13865 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13873
                                                                 =
                                                                 let uu____13876
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13876,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13873)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13865
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13878 =
                                                      let uu____13879 =
                                                        let uu____13882 =
                                                          let uu____13883 =
                                                            let uu____13886 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13886,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13883 in
                                                        (out, uu____13882) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13879 in
                                                    (uu____13878,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13736 with
                    | (data_ax,decls) ->
                        let uu____13894 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13894 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13905 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13905 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13908 =
                                 let uu____13913 =
                                   let uu____13914 =
                                     let uu____13920 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13928 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13920,
                                       uu____13928) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13914 in
                                 let uu____13936 =
                                   let uu____13938 =
                                     varops.mk_unique
                                       (Prims.strcat
                                          "fuel_guarded_inversion_"
                                          t.FStar_Ident.str) in
                                   Some uu____13938 in
                                 (uu____13913, (Some "inversion axiom"),
                                   uu____13936) in
                               FStar_SMTEncoding_Term.Assume uu____13908 in
                             let pattern_guarded_inversion =
                               let uu____13943 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13943
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13951 =
                                   let uu____13952 =
                                     let uu____13957 =
                                       let uu____13958 =
                                         let uu____13964 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13972 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13964, uu____13972) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13958 in
                                     let uu____13980 =
                                       let uu____13982 =
                                         varops.mk_unique
                                           (Prims.strcat
                                              "pattern_guarded_inversion_"
                                              t.FStar_Ident.str) in
                                       Some uu____13982 in
                                     (uu____13957, (Some "inversion axiom"),
                                       uu____13980) in
                                   FStar_SMTEncoding_Term.Assume uu____13952 in
                                 [uu____13951]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13986 =
            let uu____13994 =
              let uu____13995 = FStar_Syntax_Subst.compress k in
              uu____13995.FStar_Syntax_Syntax.n in
            match uu____13994 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14024 -> (tps, k) in
          (match uu____13986 with
           | (formals,res) ->
               let uu____14039 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14039 with
                | (formals1,res1) ->
                    let uu____14046 = encode_binders None formals1 env in
                    (match uu____14046 with
                     | (vars,guards,env',binder_decls,uu____14061) ->
                         let uu____14068 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14068 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14081 =
                                  let uu____14085 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14085) in
                                FStar_SMTEncoding_Util.mkApp uu____14081 in
                              let uu____14090 =
                                let tname_decl =
                                  let uu____14096 =
                                    let uu____14097 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14112  ->
                                              match uu____14112 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14120 = varops.next_id () in
                                    (tname, uu____14097,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14120, false) in
                                  constructor_or_logic_type_decl uu____14096 in
                                let uu____14125 =
                                  match vars with
                                  | [] ->
                                      let uu____14132 =
                                        let uu____14133 =
                                          let uu____14135 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14135 in
                                        push_free_var env1 t tname
                                          uu____14133 in
                                      ([], uu____14132)
                                  | uu____14139 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14145 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14145 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14154 =
                                          let uu____14159 =
                                            let uu____14160 =
                                              let uu____14168 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14168) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14160 in
                                          (uu____14159,
                                            (Some "name-token correspondence"),
                                            (Some
                                               (Prims.strcat
                                                  "token_correspondence_"
                                                  ttok))) in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____14154 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14125 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14090 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14192 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14192 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14206 =
                                               let uu____14207 =
                                                 let uu____14212 =
                                                   let uu____14213 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14213 in
                                                 (uu____14212,
                                                   (Some "kinding"),
                                                   (Some
                                                      (Prims.strcat
                                                         "pre_kinding_" ttok))) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14207 in
                                             [uu____14206]
                                           else [] in
                                         let uu____14217 =
                                           let uu____14219 =
                                             let uu____14221 =
                                               let uu____14222 =
                                                 let uu____14227 =
                                                   let uu____14228 =
                                                     let uu____14234 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14234) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14228 in
                                                 (uu____14227, None,
                                                   (Some
                                                      (Prims.strcat
                                                         "kinding_" ttok))) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14222 in
                                             [uu____14221] in
                                           FStar_List.append karr uu____14219 in
                                         FStar_List.append decls1 uu____14217 in
                                   let aux =
                                     let uu____14244 =
                                       let uu____14246 =
                                         inversion_axioms tapp vars in
                                       let uu____14248 =
                                         let uu____14250 =
                                           pretype_axiom tapp vars in
                                         [uu____14250] in
                                       FStar_List.append uu____14246
                                         uu____14248 in
                                     FStar_List.append kindingAx uu____14244 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14255,uu____14256,uu____14257,uu____14258,uu____14259,uu____14260,uu____14261)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14268,t,uu____14270,n_tps,quals,uu____14273,drange) ->
          let uu____14279 = new_term_constant_and_tok_from_lid env d in
          (match uu____14279 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14290 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14290 with
                | (formals,t_res) ->
                    let uu____14312 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14312 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14321 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14321 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14359 =
                                            mk_term_projector_name d x in
                                          (uu____14359,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14361 =
                                  let uu____14371 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14371, true) in
                                FStar_All.pipe_right uu____14361
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
                              let uu____14393 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14393 with
                               | (tok_typing,decls3) ->
                                   let uu____14400 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14400 with
                                    | (vars',guards',env'',decls_formals,uu____14415)
                                        ->
                                        let uu____14422 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14422 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14441 ->
                                                   let uu____14445 =
                                                     let uu____14446 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14446 in
                                                   [uu____14445] in
                                             let encode_elim uu____14453 =
                                               let uu____14454 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14454 with
                                               | (head1,args) ->
                                                   let uu____14483 =
                                                     let uu____14484 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14484.FStar_Syntax_Syntax.n in
                                                   (match uu____14483 with
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
                                                        let uu____14502 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14502
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
                                                                 | uu____14528
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14536
                                                                    =
                                                                    let uu____14537
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14537 in
                                                                    if
                                                                    uu____14536
                                                                    then
                                                                    let uu____14544
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14544]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14546
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14559
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14559
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14581
                                                                    =
                                                                    let uu____14585
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14585 in
                                                                    (match uu____14581
                                                                    with
                                                                    | 
                                                                    (uu____14592,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14598
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14598
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14600
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14600
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
                                                             (match uu____14546
                                                              with
                                                              | (uu____14608,arg_vars,elim_eqns_or_guards,uu____14611)
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
                                                                    let uu____14630
                                                                    =
                                                                    let uu____14635
                                                                    =
                                                                    let uu____14636
                                                                    =
                                                                    let uu____14642
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14648
                                                                    =
                                                                    let uu____14649
                                                                    =
                                                                    let uu____14652
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14652) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14649 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14642,
                                                                    uu____14648) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14636 in
                                                                    (uu____14635,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14630 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14666
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14666,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14668
                                                                    =
                                                                    let uu____14673
                                                                    =
                                                                    let uu____14674
                                                                    =
                                                                    let uu____14680
                                                                    =
                                                                    let uu____14683
                                                                    =
                                                                    let uu____14685
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14685] in
                                                                    [uu____14683] in
                                                                    let uu____14688
                                                                    =
                                                                    let uu____14689
                                                                    =
                                                                    let uu____14692
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14693
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14692,
                                                                    uu____14693) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14689 in
                                                                    (uu____14680,
                                                                    [x],
                                                                    uu____14688) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14674 in
                                                                    let uu____14703
                                                                    =
                                                                    let uu____14705
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    Some
                                                                    uu____14705 in
                                                                    (uu____14673,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14703) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14668
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14711
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
                                                                    (let uu____14726
                                                                    =
                                                                    let uu____14727
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14727
                                                                    dapp1 in
                                                                    [uu____14726]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14711
                                                                    FStar_List.flatten in
                                                                    let uu____14731
                                                                    =
                                                                    let uu____14736
                                                                    =
                                                                    let uu____14737
                                                                    =
                                                                    let uu____14743
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14749
                                                                    =
                                                                    let uu____14750
                                                                    =
                                                                    let uu____14753
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14753) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14750 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14743,
                                                                    uu____14749) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14737 in
                                                                    (uu____14736,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14731) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14764 ->
                                                        ((let uu____14766 =
                                                            let uu____14767 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14768 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14767
                                                              uu____14768 in
                                                          FStar_Errors.warn
                                                            drange
                                                            uu____14766);
                                                         ([], []))) in
                                             let uu____14771 = encode_elim () in
                                             (match uu____14771 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14783 =
                                                      let uu____14785 =
                                                        let uu____14787 =
                                                          let uu____14789 =
                                                            let uu____14791 =
                                                              let uu____14792
                                                                =
                                                                let uu____14798
                                                                  =
                                                                  let uu____14800
                                                                    =
                                                                    let uu____14801
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14801 in
                                                                  Some
                                                                    uu____14800 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14798) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14792 in
                                                            [uu____14791] in
                                                          let uu____14804 =
                                                            let uu____14806 =
                                                              let uu____14808
                                                                =
                                                                let uu____14810
                                                                  =
                                                                  let uu____14812
                                                                    =
                                                                    let uu____14814
                                                                    =
                                                                    let uu____14816
                                                                    =
                                                                    let uu____14817
                                                                    =
                                                                    let uu____14822
                                                                    =
                                                                    let uu____14823
                                                                    =
                                                                    let uu____14829
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14829) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14823 in
                                                                    (uu____14822,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14817 in
                                                                    let uu____14837
                                                                    =
                                                                    let uu____14839
                                                                    =
                                                                    let uu____14840
                                                                    =
                                                                    let uu____14845
                                                                    =
                                                                    let uu____14846
                                                                    =
                                                                    let uu____14852
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14858
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14852,
                                                                    uu____14858) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14846 in
                                                                    (uu____14845,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14840 in
                                                                    [uu____14839] in
                                                                    uu____14816
                                                                    ::
                                                                    uu____14837 in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))))
                                                                    ::
                                                                    uu____14814 in
                                                                  FStar_List.append
                                                                    uu____14812
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14810 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14808 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14806 in
                                                          FStar_List.append
                                                            uu____14789
                                                            uu____14804 in
                                                        FStar_List.append
                                                          decls3 uu____14787 in
                                                      FStar_List.append
                                                        decls2 uu____14785 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14783 in
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
           (fun uu____14881  ->
              fun se  ->
                match uu____14881 with
                | (g,env1) ->
                    let uu____14893 = encode_sigelt env1 se in
                    (match uu____14893 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14929 =
        match uu____14929 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14947 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14952 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14952
                   then
                     let uu____14953 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14954 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14955 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14953 uu____14954 uu____14955
                   else ());
                  (let uu____14957 = encode_term t1 env1 in
                   match uu____14957 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14967 =
                         let uu____14971 =
                           let uu____14972 =
                             let uu____14973 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____14973
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____14972 in
                         new_term_constant_from_string env1 x uu____14971 in
                       (match uu____14967 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____14984 = FStar_Options.log_queries () in
                              if uu____14984
                              then
                                let uu____14986 =
                                  let uu____14987 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____14988 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____14989 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14987 uu____14988 uu____14989 in
                                Some uu____14986
                              else None in
                            let ax =
                              let a_name =
                                Some (Prims.strcat "binder_" xxsym) in
                              FStar_SMTEncoding_Term.Assume
                                (t2, a_name, a_name) in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax]) in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15002,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15011 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15011 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____15030 = encode_sigelt env1 se in
                 (match uu____15030 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15040 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15040 with | (uu____15052,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15097  ->
            match uu____15097 with
            | (l,uu____15104,uu____15105) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15126  ->
            match uu____15126 with
            | (l,uu____15134,uu____15135) ->
                let uu____15140 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____15141 =
                  let uu____15143 =
                    let uu____15144 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15144 in
                  [uu____15143] in
                uu____15140 :: uu____15141)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15155 =
      let uu____15157 =
        let uu____15158 = FStar_Util.smap_create (Prims.parse_int "100") in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15158;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true
        } in
      [uu____15157] in
    FStar_ST.write last_env uu____15155
let get_env: FStar_TypeChecker_Env.env -> env_t =
  fun tcenv  ->
    let uu____15176 = FStar_ST.read last_env in
    match uu____15176 with
    | [] -> failwith "No env; call init first!"
    | e::uu____15182 ->
        let uu___161_15184 = e in
        {
          bindings = (uu___161_15184.bindings);
          depth = (uu___161_15184.depth);
          tcenv;
          warn = (uu___161_15184.warn);
          cache = (uu___161_15184.cache);
          nolabels = (uu___161_15184.nolabels);
          use_zfuel_name = (uu___161_15184.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___161_15184.encode_non_total_function_typ)
        }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15188 = FStar_ST.read last_env in
    match uu____15188 with
    | [] -> failwith "Empty env stack"
    | uu____15193::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15201  ->
    let uu____15202 = FStar_ST.read last_env in
    match uu____15202 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___162_15223 = hd1 in
          {
            bindings = (uu___162_15223.bindings);
            depth = (uu___162_15223.depth);
            tcenv = (uu___162_15223.tcenv);
            warn = (uu___162_15223.warn);
            cache = refs;
            nolabels = (uu___162_15223.nolabels);
            use_zfuel_name = (uu___162_15223.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_15223.encode_non_total_function_typ)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15229  ->
    let uu____15230 = FStar_ST.read last_env in
    match uu____15230 with
    | [] -> failwith "Popping an empty stack"
    | uu____15235::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15243  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15246  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15249  ->
    let uu____15250 = FStar_ST.read last_env in
    match uu____15250 with
    | hd1::uu____15256::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15262 -> failwith "Impossible"
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
        let uu____15307 = FStar_Options.log_queries () in
        if uu____15307
        then
          let uu____15309 =
            let uu____15310 =
              let uu____15311 =
                let uu____15312 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15312 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15311 in
            FStar_SMTEncoding_Term.Caption uu____15310 in
          uu____15309 :: decls
        else decls in
      let env = get_env tcenv in
      let uu____15319 = encode_sigelt env se in
      match uu____15319 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15325 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15325))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15336 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15336
       then
         let uu____15337 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15337
       else ());
      (let env = get_env tcenv in
       let uu____15342 =
         encode_signature
           (let uu___163_15346 = env in
            {
              bindings = (uu___163_15346.bindings);
              depth = (uu___163_15346.depth);
              tcenv = (uu___163_15346.tcenv);
              warn = false;
              cache = (uu___163_15346.cache);
              nolabels = (uu___163_15346.nolabels);
              use_zfuel_name = (uu___163_15346.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___163_15346.encode_non_total_function_typ)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15342 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15358 = FStar_Options.log_queries () in
             if uu____15358
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___164_15363 = env1 in
               {
                 bindings = (uu___164_15363.bindings);
                 depth = (uu___164_15363.depth);
                 tcenv = (uu___164_15363.tcenv);
                 warn = true;
                 cache = (uu___164_15363.cache);
                 nolabels = (uu___164_15363.nolabels);
                 use_zfuel_name = (uu___164_15363.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___164_15363.encode_non_total_function_typ)
               });
            (let uu____15365 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15365
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
        (let uu____15400 =
           let uu____15401 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15401.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15400);
        (let env = get_env tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15409 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15430 = aux rest in
                 (match uu____15430 with
                  | (out,rest1) ->
                      let t =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv x.FStar_Syntax_Syntax.sort in
                      let uu____15446 =
                        let uu____15448 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___165_15449 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___165_15449.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___165_15449.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t
                             }) in
                        uu____15448 :: out in
                      (uu____15446, rest1))
             | uu____15452 -> ([], bindings1) in
           let uu____15456 = aux bindings in
           match uu____15456 with
           | (closing,bindings1) ->
               let uu____15470 =
                 FStar_Syntax_Util.close_forall (FStar_List.rev closing) q in
               (uu____15470, bindings1) in
         match uu____15409 with
         | (q1,bindings1) ->
             let uu____15483 =
               let uu____15486 =
                 FStar_List.filter
                   (fun uu___134_15488  ->
                      match uu___134_15488 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15489 ->
                          false
                      | uu____15493 -> true) bindings1 in
               encode_env_bindings env uu____15486 in
             (match uu____15483 with
              | (env_decls,env1) ->
                  ((let uu____15504 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15504
                    then
                      let uu____15505 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15505
                    else ());
                   (let uu____15507 = encode_formula q1 env1 in
                    match uu____15507 with
                    | (phi,qdecls) ->
                        let uu____15519 =
                          let uu____15522 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15522 phi in
                        (match uu____15519 with
                         | (labels,phi1) ->
                             let uu____15532 = encode_labels labels in
                             (match uu____15532 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15553 =
                                      let uu____15558 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15559 =
                                        let uu____15561 =
                                          varops.mk_unique "@query" in
                                        Some uu____15561 in
                                      (uu____15558, (Some "query"),
                                        uu____15559) in
                                    FStar_SMTEncoding_Term.Assume uu____15553 in
                                  let suffix =
                                    let uu____15566 =
                                      let uu____15568 =
                                        let uu____15570 =
                                          FStar_Options.print_z3_statistics
                                            () in
                                        if uu____15570
                                        then
                                          [FStar_SMTEncoding_Term.PrintStats]
                                        else [] in
                                      FStar_List.append uu____15568
                                        [FStar_SMTEncoding_Term.Echo "Done!"] in
                                    FStar_List.append label_suffix
                                      uu____15566 in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env = get_env tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15583 = encode_formula q env in
       match uu____15583 with
       | (f,uu____15587) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15589) -> true
             | uu____15592 -> false)))