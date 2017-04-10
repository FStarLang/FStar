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
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2456) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2465 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2465, [])
       | FStar_Syntax_Syntax.Tm_type uu____2471 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2474) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2480 = encode_const c in (uu____2480, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let uu____2494 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2494 with
            | (binders1,res) ->
                let uu____2501 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2501
                then
                  let uu____2504 = encode_binders None binders1 env in
                  (match uu____2504 with
                   | (vars,guards,env',decls,uu____2519) ->
                       let fsym =
                         let uu____2529 = varops.fresh "f" in
                         (uu____2529, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2532 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___144_2536 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___144_2536.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___144_2536.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___144_2536.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___144_2536.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___144_2536.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___144_2536.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___144_2536.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___144_2536.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___144_2536.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___144_2536.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___144_2536.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___144_2536.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___144_2536.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___144_2536.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___144_2536.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___144_2536.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___144_2536.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___144_2536.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___144_2536.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___144_2536.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___144_2536.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___144_2536.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___144_2536.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2532 with
                        | (pre_opt,res_t) ->
                            let uu____2543 =
                              encode_term_pred None res_t env' app in
                            (match uu____2543 with
                             | (res_pred,decls') ->
                                 let uu____2550 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2557 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2557, [])
                                   | Some pre ->
                                       let uu____2560 =
                                         encode_formula pre env' in
                                       (match uu____2560 with
                                        | (guard,decls0) ->
                                            let uu____2568 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2568, decls0)) in
                                 (match uu____2550 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2576 =
                                          let uu____2582 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2582) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2576 in
                                      let cvars =
                                        let uu____2592 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2592
                                          (FStar_List.filter
                                             (fun uu____2598  ->
                                                match uu____2598 with
                                                | (x,uu____2602) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2613 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2613 with
                                       | Some (t',sorts,uu____2629) ->
                                           let uu____2639 =
                                             let uu____2640 =
                                               let uu____2644 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               (t', uu____2644) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2640 in
                                           (uu____2639, [])
                                       | None  ->
                                           let tsym =
                                             let uu____2660 =
                                               let uu____2661 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2661 in
                                             varops.mk_unique uu____2660 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2668 =
                                               FStar_Options.log_queries () in
                                             if uu____2668
                                             then
                                               let uu____2670 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2670
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2676 =
                                               let uu____2680 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2680) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2676 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____2688 =
                                               let uu____2692 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2692, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2688 in
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
                                             let uu____2705 =
                                               let uu____2709 =
                                                 let uu____2710 =
                                                   let uu____2716 =
                                                     let uu____2717 =
                                                       let uu____2720 =
                                                         let uu____2721 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2721 in
                                                       (f_has_t, uu____2720) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2717 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2716) in
                                                 mkForall_fuel uu____2710 in
                                               (uu____2709,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2705 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____2734 =
                                               let uu____2738 =
                                                 let uu____2739 =
                                                   let uu____2745 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2745) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2739 in
                                               (uu____2738, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2734 in
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
                     let uu____2776 =
                       let uu____2780 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____2780, (Some "Typing for non-total arrows"),
                         a_name) in
                     FStar_SMTEncoding_Term.Assume uu____2776 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____2789 =
                       let uu____2793 =
                         let uu____2794 =
                           let uu____2800 =
                             let uu____2801 =
                               let uu____2804 =
                                 let uu____2805 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2805 in
                               (f_has_t, uu____2804) in
                             FStar_SMTEncoding_Util.mkImp uu____2801 in
                           ([[f_has_t]], [fsym], uu____2800) in
                         mkForall_fuel uu____2794 in
                       (uu____2793, (Some a_name), a_name) in
                     FStar_SMTEncoding_Term.Assume uu____2789 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2819 ->
           let uu____2824 =
             let uu____2827 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2827 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2832;
                 FStar_Syntax_Syntax.pos = uu____2833;
                 FStar_Syntax_Syntax.vars = uu____2834;_} ->
                 let uu____2841 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2841 with
                  | (b,f1) ->
                      let uu____2855 =
                        let uu____2856 = FStar_List.hd b in
                        Prims.fst uu____2856 in
                      (uu____2855, f1))
             | uu____2861 -> failwith "impossible" in
           (match uu____2824 with
            | (x,f) ->
                let uu____2868 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____2868 with
                 | (base_t,decls) ->
                     let uu____2875 = gen_term_var env x in
                     (match uu____2875 with
                      | (x1,xtm,env') ->
                          let uu____2884 = encode_formula f env' in
                          (match uu____2884 with
                           | (refinement,decls') ->
                               let uu____2891 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____2891 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____2902 =
                                        let uu____2904 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____2908 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____2904
                                          uu____2908 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____2902 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____2924  ->
                                              match uu____2924 with
                                              | (y,uu____2928) ->
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
                                    let uu____2947 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2947 with
                                     | Some (t1,uu____2962,uu____2963) ->
                                         let uu____2973 =
                                           let uu____2974 =
                                             let uu____2978 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             (t1, uu____2978) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2974 in
                                         (uu____2973, [])
                                     | None  ->
                                         let tsym =
                                           let uu____2994 =
                                             let uu____2995 =
                                               FStar_Util.digest_of_string
                                                 tkey_hash in
                                             Prims.strcat "Tm_refine_"
                                               uu____2995 in
                                           varops.mk_unique uu____2994 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3004 =
                                             let uu____3008 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3008) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3004 in
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
                                           let uu____3018 =
                                             let uu____3022 =
                                               let uu____3023 =
                                                 let uu____3029 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3029) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3023 in
                                             (uu____3022,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3018 in
                                         let t_kinding =
                                           let uu____3039 =
                                             let uu____3043 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3043,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3039 in
                                         let t_interp =
                                           let uu____3053 =
                                             let uu____3057 =
                                               let uu____3058 =
                                                 let uu____3064 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3064) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3058 in
                                             let uu____3076 =
                                               let uu____3078 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3078 in
                                             (uu____3057, uu____3076,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3053 in
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
                    let uu____3122 =
                      let uu____3123 =
                        let uu____3124 =
                          let uu____3125 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3125 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3124 in
                      varops.mk_unique uu____3123 in
                    (t_has_k, (Some "Uvar typing"), uu____3122) in
                  FStar_SMTEncoding_Term.Assume uu____3118 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3131 ->
           let uu____3141 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3141 with
            | (head1,args_e) ->
                let uu____3169 =
                  let uu____3177 =
                    let uu____3178 = FStar_Syntax_Subst.compress head1 in
                    uu____3178.FStar_Syntax_Syntax.n in
                  (uu____3177, args_e) in
                (match uu____3169 with
                 | (uu____3188,uu____3189) when head_redex env head1 ->
                     let uu____3200 = whnf env t in
                     encode_term uu____3200 env
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
                     let uu____3274 = encode_term v1 env in
                     (match uu____3274 with
                      | (v11,decls1) ->
                          let uu____3281 = encode_term v2 env in
                          (match uu____3281 with
                           | (v21,decls2) ->
                               let uu____3288 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3288,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3290) ->
                     let e0 =
                       let uu____3304 =
                         let uu____3307 =
                           let uu____3308 =
                             let uu____3318 =
                               let uu____3324 = FStar_List.hd args_e in
                               [uu____3324] in
                             (head1, uu____3318) in
                           FStar_Syntax_Syntax.Tm_app uu____3308 in
                         FStar_Syntax_Syntax.mk uu____3307 in
                       uu____3304 None head1.FStar_Syntax_Syntax.pos in
                     ((let uu____3357 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3357
                       then
                         let uu____3358 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Trying to normalize %s\n"
                           uu____3358
                       else ());
                      (let e01 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Reify;
                           FStar_TypeChecker_Normalize.Eager_unfolding;
                           FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                           env.tcenv e0 in
                       (let uu____3362 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify") in
                        if uu____3362
                        then
                          let uu____3363 =
                            FStar_Syntax_Print.term_to_string e01 in
                          FStar_Util.print1 "Result of normalization %s\n"
                            uu____3363
                        else ());
                       (let e02 =
                          let uu____3366 =
                            let uu____3367 =
                              let uu____3368 =
                                FStar_Syntax_Subst.compress e01 in
                              uu____3368.FStar_Syntax_Syntax.n in
                            match uu____3367 with
                            | FStar_Syntax_Syntax.Tm_app uu____3371 -> false
                            | uu____3381 -> true in
                          if uu____3366
                          then e01
                          else
                            (let uu____3383 =
                               FStar_Syntax_Util.head_and_args e01 in
                             match uu____3383 with
                             | (head2,args) ->
                                 let uu____3409 =
                                   let uu____3410 =
                                     let uu____3411 =
                                       FStar_Syntax_Subst.compress head2 in
                                     uu____3411.FStar_Syntax_Syntax.n in
                                   match uu____3410 with
                                   | FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_reify ) -> true
                                   | uu____3414 -> false in
                                 if uu____3409
                                 then
                                   (match args with
                                    | x::[] -> Prims.fst x
                                    | uu____3430 ->
                                        failwith
                                          "Impossible : Reify applied to multiple arguments after normalization.")
                                 else e01) in
                        let e =
                          match args_e with
                          | uu____3438::[] -> e02
                          | uu____3451 ->
                              let uu____3457 =
                                let uu____3460 =
                                  let uu____3461 =
                                    let uu____3471 = FStar_List.tl args_e in
                                    (e02, uu____3471) in
                                  FStar_Syntax_Syntax.Tm_app uu____3461 in
                                FStar_Syntax_Syntax.mk uu____3460 in
                              uu____3457 None t0.FStar_Syntax_Syntax.pos in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3494),(arg,uu____3496)::[]) -> encode_term arg env
                 | uu____3514 ->
                     let uu____3522 = encode_args args_e env in
                     (match uu____3522 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3555 = encode_term head1 env in
                            match uu____3555 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3594 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3594 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3636  ->
                                                 fun uu____3637  ->
                                                   match (uu____3636,
                                                           uu____3637)
                                                   with
                                                   | ((bv,uu____3651),
                                                      (a,uu____3653)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3667 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3667
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3672 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3672 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3682 =
                                                   let uu____3686 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3691 =
                                                     let uu____3692 =
                                                       let uu____3693 =
                                                         let uu____3694 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3694 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3693 in
                                                     varops.mk_unique
                                                       uu____3692 in
                                                   (uu____3686,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3691) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3682 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3711 = lookup_free_var_sym env fv in
                            match uu____3711 with
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
                                let uu____3749 =
                                  let uu____3750 =
                                    let uu____3753 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3753 Prims.fst in
                                  FStar_All.pipe_right uu____3750 Prims.snd in
                                Some uu____3749
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3772,(FStar_Util.Inl t1,uu____3774),uu____3775)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3813,(FStar_Util.Inr c,uu____3815),uu____3816)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3854 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3874 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3874 in
                               let uu____3875 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3875 with
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
                                     | uu____3900 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3945 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3945 with
            | (bs1,body1,opening) ->
                let fallback uu____3960 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3965 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3965, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3976 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3976
                  | FStar_Util.Inr (eff,uu____3978) ->
                      let uu____3984 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3984 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body = reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4029 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___145_4030 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___145_4030.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___145_4030.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___145_4030.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___145_4030.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___145_4030.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___145_4030.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___145_4030.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___145_4030.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___145_4030.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___145_4030.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___145_4030.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___145_4030.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___145_4030.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___145_4030.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___145_4030.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___145_4030.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___145_4030.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___145_4030.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___145_4030.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___145_4030.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___145_4030.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___145_4030.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___145_4030.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4029 FStar_Syntax_Syntax.U_unknown in
                        let uu____4031 =
                          let uu____4032 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4032 in
                        FStar_Util.Inl uu____4031
                    | FStar_Util.Inr (eff_name,uu____4039) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4070 =
                        let uu____4071 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4071 in
                      FStar_All.pipe_right uu____4070
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4083 =
                        let uu____4084 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4084 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4092 =
                          let uu____4093 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4093 in
                        FStar_All.pipe_right uu____4092
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4097 =
                             let uu____4098 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4098 in
                           FStar_All.pipe_right uu____4097
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4109 =
                         let uu____4110 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4110 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4109);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4125 =
                       (is_impure lc1) &&
                         (let uu____4126 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4126) in
                     if uu____4125
                     then fallback ()
                     else
                       (let uu____4130 = encode_binders None bs1 env in
                        match uu____4130 with
                        | (vars,guards,envbody,decls,uu____4145) ->
                            let uu____4152 =
                              let uu____4160 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4160
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4152 with
                             | (lc2,body2) ->
                                 let uu____4185 = encode_term body2 envbody in
                                 (match uu____4185 with
                                  | (body3,decls') ->
                                      let key_body =
                                        let uu____4193 =
                                          let uu____4199 =
                                            let uu____4200 =
                                              let uu____4203 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____4203, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____4200 in
                                          ([], vars, uu____4199) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4193 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____4214 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____4214 with
                                       | Some (t1,uu____4229,uu____4230) ->
                                           let uu____4240 =
                                             let uu____4241 =
                                               let uu____4245 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (t1, uu____4245) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4241 in
                                           (uu____4240, [])
                                       | None  ->
                                           let uu____4256 =
                                             is_eta env vars body3 in
                                           (match uu____4256 with
                                            | Some t1 -> (t1, [])
                                            | None  ->
                                                let cvar_sorts =
                                                  FStar_List.map Prims.snd
                                                    cvars in
                                                let fsym =
                                                  let uu____4267 =
                                                    let uu____4268 =
                                                      FStar_Util.digest_of_string
                                                        tkey_hash in
                                                    Prims.strcat "Tm_abs_"
                                                      uu____4268 in
                                                  varops.mk_unique uu____4267 in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      None) in
                                                let f =
                                                  let uu____4273 =
                                                    let uu____4277 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars in
                                                    (fsym, uu____4277) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4273 in
                                                let app = mk_Apply f vars in
                                                let typing_f =
                                                  let uu____4285 =
                                                    codomain_eff lc2 in
                                                  match uu____4285 with
                                                  | None  -> []
                                                  | Some c ->
                                                      let tfun =
                                                        FStar_Syntax_Util.arrow
                                                          bs1 c in
                                                      let uu____4292 =
                                                        encode_term_pred None
                                                          tfun env f in
                                                      (match uu____4292 with
                                                       | (f_has_t,decls'') ->
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym in
                                                           let uu____4299 =
                                                             let uu____4301 =
                                                               let uu____4302
                                                                 =
                                                                 let uu____4306
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkForall
                                                                    ([[f]],
                                                                    cvars,
                                                                    f_has_t) in
                                                                 (uu____4306,
                                                                   (Some
                                                                    a_name),
                                                                   a_name) in
                                                               FStar_SMTEncoding_Term.Assume
                                                                 uu____4302 in
                                                             [uu____4301] in
                                                           FStar_List.append
                                                             decls''
                                                             uu____4299) in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____4314 =
                                                    let uu____4318 =
                                                      let uu____4319 =
                                                        let uu____4325 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars),
                                                          uu____4325) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____4319 in
                                                    (uu____4318,
                                                      (Some a_name), a_name) in
                                                  FStar_SMTEncoding_Term.Assume
                                                    uu____4314 in
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
           ((uu____4343,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4344;
                          FStar_Syntax_Syntax.lbunivs = uu____4345;
                          FStar_Syntax_Syntax.lbtyp = uu____4346;
                          FStar_Syntax_Syntax.lbeff = uu____4347;
                          FStar_Syntax_Syntax.lbdef = uu____4348;_}::uu____4349),uu____4350)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4368;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4370;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4386 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4399 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4399, [decl_e])))
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
              let uu____4441 = encode_term e1 env in
              match uu____4441 with
              | (ee1,decls1) ->
                  let uu____4448 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4448 with
                   | (xs,e21) ->
                       let uu____4462 = FStar_List.hd xs in
                       (match uu____4462 with
                        | (x1,uu____4470) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4472 = encode_body e21 env' in
                            (match uu____4472 with
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
            let uu____4494 =
              let uu____4498 =
                let uu____4499 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4499 in
              gen_term_var env uu____4498 in
            match uu____4494 with
            | (scrsym,scr',env1) ->
                let uu____4513 = encode_term e env1 in
                (match uu____4513 with
                 | (scr,decls) ->
                     let uu____4520 =
                       let encode_branch b uu____4536 =
                         match uu____4536 with
                         | (else_case,decls1) ->
                             let uu____4547 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4547 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4577  ->
                                       fun uu____4578  ->
                                         match (uu____4577, uu____4578) with
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
                                                       fun uu____4615  ->
                                                         match uu____4615
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4620 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4635 =
                                                     encode_term w1 env2 in
                                                   (match uu____4635 with
                                                    | (w2,decls21) ->
                                                        let uu____4643 =
                                                          let uu____4644 =
                                                            let uu____4647 =
                                                              let uu____4648
                                                                =
                                                                let uu____4651
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4651) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4648 in
                                                            (guard,
                                                              uu____4647) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4644 in
                                                        (uu____4643, decls21)) in
                                             (match uu____4620 with
                                              | (guard1,decls21) ->
                                                  let uu____4659 =
                                                    encode_br br env2 in
                                                  (match uu____4659 with
                                                   | (br1,decls3) ->
                                                       let uu____4667 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4667,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4520 with
                      | (match_tm,decls1) ->
                          let uu____4679 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4679, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4710 -> let uu____4711 = encode_one_pat env pat in [uu____4711]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4723 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4723
       then
         let uu____4724 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4724
       else ());
      (let uu____4726 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4726 with
       | (vars,pat_term) ->
           let uu____4736 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4759  ->
                     fun v1  ->
                       match uu____4759 with
                       | (env1,vars1) ->
                           let uu____4787 = gen_term_var env1 v1 in
                           (match uu____4787 with
                            | (xx,uu____4799,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4736 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4846 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4854 =
                        let uu____4857 = encode_const c in
                        (scrutinee, uu____4857) in
                      FStar_SMTEncoding_Util.mkEq uu____4854
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4876 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4876 with
                        | (uu____4880,uu____4881::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4883 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4904  ->
                                  match uu____4904 with
                                  | (arg,uu____4910) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4920 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4920)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4939 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4954 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4969 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4991  ->
                                  match uu____4991 with
                                  | (arg,uu____5000) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5010 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5010)) in
                      FStar_All.pipe_right uu____4969 FStar_List.flatten in
                let pat_term1 uu____5026 = encode_term pat_term env1 in
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
      let uu____5033 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5048  ->
                fun uu____5049  ->
                  match (uu____5048, uu____5049) with
                  | ((tms,decls),(t,uu____5069)) ->
                      let uu____5080 = encode_term t env in
                      (match uu____5080 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5033 with | (l1,decls) -> ((FStar_List.rev l1), decls)
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
            let uu____5118 = FStar_Syntax_Util.list_elements e in
            match uu____5118 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 []) in
          let one_pat p =
            let uu____5136 =
              let uu____5146 = FStar_Syntax_Util.unmeta p in
              FStar_All.pipe_right uu____5146 FStar_Syntax_Util.head_and_args in
            match uu____5136 with
            | (head1,args) ->
                let uu____5177 =
                  let uu____5185 =
                    let uu____5186 = FStar_Syntax_Util.un_uinst head1 in
                    uu____5186.FStar_Syntax_Syntax.n in
                  (uu____5185, args) in
                (match uu____5177 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5200,uu____5201)::(e,uu____5203)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5234)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5255 -> failwith "Unexpected pattern term") in
          let lemma_pats p =
            let elts = list_elements1 p in
            let smt_pat_or t1 =
              let uu____5288 =
                let uu____5298 = FStar_Syntax_Util.unmeta t1 in
                FStar_All.pipe_right uu____5298
                  FStar_Syntax_Util.head_and_args in
              match uu____5288 with
              | (head1,args) ->
                  let uu____5327 =
                    let uu____5335 =
                      let uu____5336 = FStar_Syntax_Util.un_uinst head1 in
                      uu____5336.FStar_Syntax_Syntax.n in
                    (uu____5335, args) in
                  (match uu____5327 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5349)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5369 -> None) in
            match elts with
            | t1::[] ->
                let uu____5387 = smt_pat_or t1 in
                (match uu____5387 with
                 | Some e ->
                     let uu____5403 = list_elements1 e in
                     FStar_All.pipe_right uu____5403
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5420 = list_elements1 branch1 in
                             FStar_All.pipe_right uu____5420
                               (FStar_List.map one_pat)))
                 | uu____5434 ->
                     let uu____5438 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat) in
                     [uu____5438])
            | uu____5469 ->
                let uu____5471 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat) in
                [uu____5471] in
          let uu____5502 =
            let uu____5518 =
              let uu____5519 = FStar_Syntax_Subst.compress t in
              uu____5519.FStar_Syntax_Syntax.n in
            match uu____5518 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5549 = FStar_Syntax_Subst.open_comp binders c in
                (match uu____5549 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5584;
                            FStar_Syntax_Syntax.effect_name = uu____5585;
                            FStar_Syntax_Syntax.result_typ = uu____5586;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5588)::(post,uu____5590)::(pats,uu____5592)::[];
                            FStar_Syntax_Syntax.flags = uu____5593;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats in
                          let uu____5627 = lemma_pats pats' in
                          (binders1, pre, post, uu____5627)
                      | uu____5646 -> failwith "impos"))
            | uu____5662 -> failwith "Impos" in
          match uu____5502 with
          | (binders,pre,post,patterns) ->
              let uu____5706 = encode_binders None binders env in
              (match uu____5706 with
               | (vars,guards,env1,decls,uu____5721) ->
                   let uu____5728 =
                     let uu____5735 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5766 =
                                 let uu____5771 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5787  ->
                                           match uu____5787 with
                                           | (t1,uu____5794) ->
                                               encode_term t1
                                                 (let uu___146_5797 = env1 in
                                                  {
                                                    bindings =
                                                      (uu___146_5797.bindings);
                                                    depth =
                                                      (uu___146_5797.depth);
                                                    tcenv =
                                                      (uu___146_5797.tcenv);
                                                    warn =
                                                      (uu___146_5797.warn);
                                                    cache =
                                                      (uu___146_5797.cache);
                                                    nolabels =
                                                      (uu___146_5797.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___146_5797.encode_non_total_function_typ)
                                                  }))) in
                                 FStar_All.pipe_right uu____5771
                                   FStar_List.unzip in
                               match uu____5766 with
                               | (pats,decls1) -> (pats, decls1))) in
                     FStar_All.pipe_right uu____5735 FStar_List.unzip in
                   (match uu____5728 with
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
                                           let uu____5861 =
                                             let uu____5862 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5862 e in
                                           uu____5861 :: p))
                               | uu____5863 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5892 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e in
                                                 uu____5892 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5900 =
                                           let uu____5901 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort) in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5901 tl1 in
                                         aux uu____5900 vars2
                                     | uu____5902 -> pats in
                                   let uu____5906 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort) in
                                   aux uu____5906 vars) in
                        let env2 =
                          let uu___147_5908 = env1 in
                          {
                            bindings = (uu___147_5908.bindings);
                            depth = (uu___147_5908.depth);
                            tcenv = (uu___147_5908.tcenv);
                            warn = (uu___147_5908.warn);
                            cache = (uu___147_5908.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___147_5908.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___147_5908.encode_non_total_function_typ)
                          } in
                        let uu____5909 =
                          let uu____5912 = FStar_Syntax_Util.unmeta pre in
                          encode_formula uu____5912 env2 in
                        (match uu____5909 with
                         | (pre1,decls'') ->
                             let uu____5917 =
                               let uu____5920 = FStar_Syntax_Util.unmeta post in
                               encode_formula uu____5920 env2 in
                             (match uu____5917 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls''')) in
                                  let uu____5927 =
                                    let uu____5928 =
                                      let uu____5934 =
                                        let uu____5935 =
                                          let uu____5938 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards) in
                                          (uu____5938, post1) in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5935 in
                                      (pats1, vars, uu____5934) in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5928 in
                                  (uu____5927, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5951 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5951
        then
          let uu____5952 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5953 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5952 uu____5953
        else () in
      let enc f r l =
        let uu____5980 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5993 = encode_term (Prims.fst x) env in
                 match uu____5993 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5980 with
        | (decls,args) ->
            let uu____6010 =
              let uu___148_6011 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___148_6011.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___148_6011.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6010, decls) in
      let const_op f r uu____6030 = let uu____6033 = f r in (uu____6033, []) in
      let un_op f l =
        let uu____6049 = FStar_List.hd l in FStar_All.pipe_left f uu____6049 in
      let bin_op f uu___120_6062 =
        match uu___120_6062 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6070 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6097 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6106  ->
                 match uu____6106 with
                 | (t,uu____6114) ->
                     let uu____6115 = encode_formula t env in
                     (match uu____6115 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6097 with
        | (decls,phis) ->
            let uu____6132 =
              let uu___149_6133 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___149_6133.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___149_6133.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6132, decls) in
      let eq_op r uu___121_6149 =
        match uu___121_6149 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6209 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6209 r [e1; e2]
        | l ->
            let uu____6229 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6229 r l in
      let mk_imp1 r uu___122_6248 =
        match uu___122_6248 with
        | (lhs,uu____6252)::(rhs,uu____6254)::[] ->
            let uu____6275 = encode_formula rhs env in
            (match uu____6275 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6284) ->
                      (l1, decls1)
                  | uu____6287 ->
                      let uu____6288 = encode_formula lhs env in
                      (match uu____6288 with
                       | (l2,decls2) ->
                           let uu____6295 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6295, (FStar_List.append decls1 decls2)))))
        | uu____6297 -> failwith "impossible" in
      let mk_ite r uu___123_6312 =
        match uu___123_6312 with
        | (guard,uu____6316)::(_then,uu____6318)::(_else,uu____6320)::[] ->
            let uu____6349 = encode_formula guard env in
            (match uu____6349 with
             | (g,decls1) ->
                 let uu____6356 = encode_formula _then env in
                 (match uu____6356 with
                  | (t,decls2) ->
                      let uu____6363 = encode_formula _else env in
                      (match uu____6363 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6372 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6391 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6391 in
      let connectives =
        let uu____6403 =
          let uu____6412 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6412) in
        let uu____6425 =
          let uu____6435 =
            let uu____6444 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6444) in
          let uu____6457 =
            let uu____6467 =
              let uu____6477 =
                let uu____6486 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6486) in
              let uu____6499 =
                let uu____6509 =
                  let uu____6519 =
                    let uu____6528 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6528) in
                  [uu____6519;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6509 in
              uu____6477 :: uu____6499 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6467 in
          uu____6435 :: uu____6457 in
        uu____6403 :: uu____6425 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6690 = encode_formula phi' env in
            (match uu____6690 with
             | (phi2,decls) ->
                 let uu____6697 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6697, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6698 ->
            let uu____6703 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6703 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6732 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6732 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6740;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6742;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6758 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6758 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6790::(x,uu____6792)::(t,uu____6794)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6828 = encode_term x env in
                 (match uu____6828 with
                  | (x1,decls) ->
                      let uu____6835 = encode_term t env in
                      (match uu____6835 with
                       | (t1,decls') ->
                           let uu____6842 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6842, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6846)::(msg,uu____6848)::(phi2,uu____6850)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6884 =
                   let uu____6887 =
                     let uu____6888 = FStar_Syntax_Subst.compress r in
                     uu____6888.FStar_Syntax_Syntax.n in
                   let uu____6891 =
                     let uu____6892 = FStar_Syntax_Subst.compress msg in
                     uu____6892.FStar_Syntax_Syntax.n in
                   (uu____6887, uu____6891) in
                 (match uu____6884 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6899))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6915 -> fallback phi2)
             | uu____6918 when head_redex env head2 ->
                 let uu____6926 = whnf env phi1 in
                 encode_formula uu____6926 env
             | uu____6927 ->
                 let uu____6935 = encode_term phi1 env in
                 (match uu____6935 with
                  | (tt,decls) ->
                      let uu____6942 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___150_6943 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___150_6943.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___150_6943.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6942, decls)))
        | uu____6946 ->
            let uu____6947 = encode_term phi1 env in
            (match uu____6947 with
             | (tt,decls) ->
                 let uu____6954 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___151_6955 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___151_6955.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___151_6955.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6954, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6982 = encode_binders None bs env1 in
        match uu____6982 with
        | (vars,guards,env2,decls,uu____7004) ->
            let uu____7011 =
              let uu____7018 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7041 =
                          let uu____7046 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7060  ->
                                    match uu____7060 with
                                    | (t,uu____7066) ->
                                        encode_term t
                                          (let uu___152_7067 = env2 in
                                           {
                                             bindings =
                                               (uu___152_7067.bindings);
                                             depth = (uu___152_7067.depth);
                                             tcenv = (uu___152_7067.tcenv);
                                             warn = (uu___152_7067.warn);
                                             cache = (uu___152_7067.cache);
                                             nolabels =
                                               (uu___152_7067.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___152_7067.encode_non_total_function_typ)
                                           }))) in
                          FStar_All.pipe_right uu____7046 FStar_List.unzip in
                        match uu____7041 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7018 FStar_List.unzip in
            (match uu____7011 with
             | (pats,decls') ->
                 let uu____7119 = encode_formula body env2 in
                 (match uu____7119 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7138;
                             FStar_SMTEncoding_Term.rng = uu____7139;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7147 -> guards in
                      let uu____7150 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7150, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7184  ->
                   match uu____7184 with
                   | (x,uu____7188) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7194 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7200 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7200) uu____7194 tl1 in
             let uu____7202 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7214  ->
                       match uu____7214 with
                       | (b,uu____7218) ->
                           let uu____7219 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7219)) in
             (match uu____7202 with
              | None  -> ()
              | Some (x,uu____7223) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7233 =
                    let uu____7234 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7234 in
                  FStar_Errors.warn pos uu____7233) in
       let uu____7235 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7235 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7241 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7277  ->
                     match uu____7277 with
                     | (l,uu____7287) -> FStar_Ident.lid_equals op l)) in
           (match uu____7241 with
            | None  -> fallback phi1
            | Some (uu____7310,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7339 = encode_q_body env vars pats body in
             match uu____7339 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7365 =
                     let uu____7371 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7371) in
                   FStar_SMTEncoding_Term.mkForall uu____7365
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7383 = encode_q_body env vars pats body in
             match uu____7383 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7408 =
                   let uu____7409 =
                     let uu____7415 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7415) in
                   FStar_SMTEncoding_Term.mkExists uu____7409
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7408, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7464 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7464 with
  | (asym,a) ->
      let uu____7469 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7469 with
       | (xsym,x) ->
           let uu____7474 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7474 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7504 =
                      let uu____7510 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7510, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7504 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7525 =
                      let uu____7529 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7529) in
                    FStar_SMTEncoding_Util.mkApp uu____7525 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7537 =
                    let uu____7539 =
                      let uu____7541 =
                        let uu____7543 =
                          let uu____7544 =
                            let uu____7548 =
                              let uu____7549 =
                                let uu____7555 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7555) in
                              FStar_SMTEncoding_Util.mkForall uu____7549 in
                            (uu____7548, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Term.Assume uu____7544 in
                        let uu____7564 =
                          let uu____7566 =
                            let uu____7567 =
                              let uu____7571 =
                                let uu____7572 =
                                  let uu____7578 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7578) in
                                FStar_SMTEncoding_Util.mkForall uu____7572 in
                              (uu____7571,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Term.Assume uu____7567 in
                          [uu____7566] in
                        uu____7543 :: uu____7564 in
                      xtok_decl :: uu____7541 in
                    xname_decl :: uu____7539 in
                  (xtok1, uu____7537) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7627 =
                    let uu____7635 =
                      let uu____7641 =
                        let uu____7642 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7642 in
                      quant axy uu____7641 in
                    (FStar_Syntax_Const.op_Eq, uu____7635) in
                  let uu____7648 =
                    let uu____7657 =
                      let uu____7665 =
                        let uu____7671 =
                          let uu____7672 =
                            let uu____7673 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7673 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7672 in
                        quant axy uu____7671 in
                      (FStar_Syntax_Const.op_notEq, uu____7665) in
                    let uu____7679 =
                      let uu____7688 =
                        let uu____7696 =
                          let uu____7702 =
                            let uu____7703 =
                              let uu____7704 =
                                let uu____7707 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7708 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7707, uu____7708) in
                              FStar_SMTEncoding_Util.mkLT uu____7704 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7703 in
                          quant xy uu____7702 in
                        (FStar_Syntax_Const.op_LT, uu____7696) in
                      let uu____7714 =
                        let uu____7723 =
                          let uu____7731 =
                            let uu____7737 =
                              let uu____7738 =
                                let uu____7739 =
                                  let uu____7742 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7743 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7742, uu____7743) in
                                FStar_SMTEncoding_Util.mkLTE uu____7739 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7738 in
                            quant xy uu____7737 in
                          (FStar_Syntax_Const.op_LTE, uu____7731) in
                        let uu____7749 =
                          let uu____7758 =
                            let uu____7766 =
                              let uu____7772 =
                                let uu____7773 =
                                  let uu____7774 =
                                    let uu____7777 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7778 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7777, uu____7778) in
                                  FStar_SMTEncoding_Util.mkGT uu____7774 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7773 in
                              quant xy uu____7772 in
                            (FStar_Syntax_Const.op_GT, uu____7766) in
                          let uu____7784 =
                            let uu____7793 =
                              let uu____7801 =
                                let uu____7807 =
                                  let uu____7808 =
                                    let uu____7809 =
                                      let uu____7812 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7813 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7812, uu____7813) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7809 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7808 in
                                quant xy uu____7807 in
                              (FStar_Syntax_Const.op_GTE, uu____7801) in
                            let uu____7819 =
                              let uu____7828 =
                                let uu____7836 =
                                  let uu____7842 =
                                    let uu____7843 =
                                      let uu____7844 =
                                        let uu____7847 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7848 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7847, uu____7848) in
                                      FStar_SMTEncoding_Util.mkSub uu____7844 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7843 in
                                  quant xy uu____7842 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7836) in
                              let uu____7854 =
                                let uu____7863 =
                                  let uu____7871 =
                                    let uu____7877 =
                                      let uu____7878 =
                                        let uu____7879 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7879 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7878 in
                                    quant qx uu____7877 in
                                  (FStar_Syntax_Const.op_Minus, uu____7871) in
                                let uu____7885 =
                                  let uu____7894 =
                                    let uu____7902 =
                                      let uu____7908 =
                                        let uu____7909 =
                                          let uu____7910 =
                                            let uu____7913 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7914 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7913, uu____7914) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7910 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7909 in
                                      quant xy uu____7908 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7902) in
                                  let uu____7920 =
                                    let uu____7929 =
                                      let uu____7937 =
                                        let uu____7943 =
                                          let uu____7944 =
                                            let uu____7945 =
                                              let uu____7948 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7949 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7948, uu____7949) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7945 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7944 in
                                        quant xy uu____7943 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7937) in
                                    let uu____7955 =
                                      let uu____7964 =
                                        let uu____7972 =
                                          let uu____7978 =
                                            let uu____7979 =
                                              let uu____7980 =
                                                let uu____7983 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7984 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7983, uu____7984) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7980 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7979 in
                                          quant xy uu____7978 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7972) in
                                      let uu____7990 =
                                        let uu____7999 =
                                          let uu____8007 =
                                            let uu____8013 =
                                              let uu____8014 =
                                                let uu____8015 =
                                                  let uu____8018 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8019 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8018, uu____8019) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8015 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8014 in
                                            quant xy uu____8013 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8007) in
                                        let uu____8025 =
                                          let uu____8034 =
                                            let uu____8042 =
                                              let uu____8048 =
                                                let uu____8049 =
                                                  let uu____8050 =
                                                    let uu____8053 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8054 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8053, uu____8054) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8050 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8049 in
                                              quant xy uu____8048 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8042) in
                                          let uu____8060 =
                                            let uu____8069 =
                                              let uu____8077 =
                                                let uu____8083 =
                                                  let uu____8084 =
                                                    let uu____8085 =
                                                      let uu____8088 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8089 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8088,
                                                        uu____8089) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8085 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8084 in
                                                quant xy uu____8083 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8077) in
                                            let uu____8095 =
                                              let uu____8104 =
                                                let uu____8112 =
                                                  let uu____8118 =
                                                    let uu____8119 =
                                                      let uu____8120 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8120 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8119 in
                                                  quant qx uu____8118 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8112) in
                                              [uu____8104] in
                                            uu____8069 :: uu____8095 in
                                          uu____8034 :: uu____8060 in
                                        uu____7999 :: uu____8025 in
                                      uu____7964 :: uu____7990 in
                                    uu____7929 :: uu____7955 in
                                  uu____7894 :: uu____7920 in
                                uu____7863 :: uu____7885 in
                              uu____7828 :: uu____7854 in
                            uu____7793 :: uu____7819 in
                          uu____7758 :: uu____7784 in
                        uu____7723 :: uu____7749 in
                      uu____7688 :: uu____7714 in
                    uu____7657 :: uu____7679 in
                  uu____7627 :: uu____7648 in
                let mk1 l v1 =
                  let uu____8248 =
                    let uu____8253 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8285  ->
                              match uu____8285 with
                              | (l',uu____8294) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8253
                      (FStar_Option.map
                         (fun uu____8327  ->
                            match uu____8327 with | (uu____8338,b) -> b v1)) in
                  FStar_All.pipe_right uu____8248 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8379  ->
                          match uu____8379 with
                          | (l',uu____8388) -> FStar_Ident.lid_equals l l')) in
                { mk = mk1; is }))
let pretype_axiom:
  FStar_SMTEncoding_Term.term ->
    (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.decl
  =
  fun tapp  ->
    fun vars  ->
      let uu____8411 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      match uu____8411 with
      | (xxsym,xx) ->
          let uu____8416 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
          (match uu____8416 with
           | (ffsym,ff) ->
               let xx_has_type =
                 FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
               let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
               let uu____8423 =
                 let uu____8427 =
                   let uu____8428 =
                     let uu____8434 =
                       let uu____8435 =
                         let uu____8438 =
                           let uu____8439 =
                             let uu____8442 =
                               FStar_SMTEncoding_Util.mkApp ("PreType", [xx]) in
                             (tapp, uu____8442) in
                           FStar_SMTEncoding_Util.mkEq uu____8439 in
                         (xx_has_type, uu____8438) in
                       FStar_SMTEncoding_Util.mkImp uu____8435 in
                     ([[xx_has_type]],
                       ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                       (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                       uu____8434) in
                   FStar_SMTEncoding_Util.mkForall uu____8428 in
                 let uu____8455 =
                   let uu____8456 =
                     let uu____8457 = FStar_Util.digest_of_string tapp_hash in
                     Prims.strcat "pretyping_" uu____8457 in
                   varops.mk_unique uu____8456 in
                 (uu____8427, (Some "pretyping"), uu____8455) in
               FStar_SMTEncoding_Term.Assume uu____8423)
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
    let uu____8487 =
      let uu____8488 =
        let uu____8492 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8492, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Term.Assume uu____8488 in
    let uu____8494 =
      let uu____8496 =
        let uu____8497 =
          let uu____8501 =
            let uu____8502 =
              let uu____8508 =
                let uu____8509 =
                  let uu____8512 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8512) in
                FStar_SMTEncoding_Util.mkImp uu____8509 in
              ([[typing_pred]], [xx], uu____8508) in
            mkForall_fuel uu____8502 in
          (uu____8501, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8497 in
      [uu____8496] in
    uu____8487 :: uu____8494 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8540 =
      let uu____8541 =
        let uu____8545 =
          let uu____8546 =
            let uu____8552 =
              let uu____8555 =
                let uu____8557 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8557] in
              [uu____8555] in
            let uu____8560 =
              let uu____8561 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8561 tt in
            (uu____8552, [bb], uu____8560) in
          FStar_SMTEncoding_Util.mkForall uu____8546 in
        (uu____8545, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Term.Assume uu____8541 in
    let uu____8572 =
      let uu____8574 =
        let uu____8575 =
          let uu____8579 =
            let uu____8580 =
              let uu____8586 =
                let uu____8587 =
                  let uu____8590 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8590) in
                FStar_SMTEncoding_Util.mkImp uu____8587 in
              ([[typing_pred]], [xx], uu____8586) in
            mkForall_fuel uu____8580 in
          (uu____8579, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8575 in
      [uu____8574] in
    uu____8540 :: uu____8572 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8624 =
        let uu____8625 =
          let uu____8629 =
            let uu____8631 =
              let uu____8633 =
                let uu____8635 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8636 =
                  let uu____8638 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8638] in
                uu____8635 :: uu____8636 in
              tt :: uu____8633 in
            tt :: uu____8631 in
          ("Prims.Precedes", uu____8629) in
        FStar_SMTEncoding_Util.mkApp uu____8625 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8624 in
    let precedes_y_x =
      let uu____8641 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8641 in
    let uu____8643 =
      let uu____8644 =
        let uu____8648 =
          let uu____8649 =
            let uu____8655 =
              let uu____8658 =
                let uu____8660 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8660] in
              [uu____8658] in
            let uu____8663 =
              let uu____8664 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8664 tt in
            (uu____8655, [bb], uu____8663) in
          FStar_SMTEncoding_Util.mkForall uu____8649 in
        (uu____8648, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Term.Assume uu____8644 in
    let uu____8675 =
      let uu____8677 =
        let uu____8678 =
          let uu____8682 =
            let uu____8683 =
              let uu____8689 =
                let uu____8690 =
                  let uu____8693 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8693) in
                FStar_SMTEncoding_Util.mkImp uu____8690 in
              ([[typing_pred]], [xx], uu____8689) in
            mkForall_fuel uu____8683 in
          (uu____8682, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8678 in
      let uu____8706 =
        let uu____8708 =
          let uu____8709 =
            let uu____8713 =
              let uu____8714 =
                let uu____8720 =
                  let uu____8721 =
                    let uu____8724 =
                      let uu____8725 =
                        let uu____8727 =
                          let uu____8729 =
                            let uu____8731 =
                              let uu____8732 =
                                let uu____8735 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8736 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8735, uu____8736) in
                              FStar_SMTEncoding_Util.mkGT uu____8732 in
                            let uu____8737 =
                              let uu____8739 =
                                let uu____8740 =
                                  let uu____8743 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8744 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8743, uu____8744) in
                                FStar_SMTEncoding_Util.mkGTE uu____8740 in
                              let uu____8745 =
                                let uu____8747 =
                                  let uu____8748 =
                                    let uu____8751 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8752 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8751, uu____8752) in
                                  FStar_SMTEncoding_Util.mkLT uu____8748 in
                                [uu____8747] in
                              uu____8739 :: uu____8745 in
                            uu____8731 :: uu____8737 in
                          typing_pred_y :: uu____8729 in
                        typing_pred :: uu____8727 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8725 in
                    (uu____8724, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8721 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8720) in
              mkForall_fuel uu____8714 in
            (uu____8713, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Term.Assume uu____8709 in
        [uu____8708] in
      uu____8677 :: uu____8706 in
    uu____8643 :: uu____8675 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8782 =
      let uu____8783 =
        let uu____8787 =
          let uu____8788 =
            let uu____8794 =
              let uu____8797 =
                let uu____8799 = FStar_SMTEncoding_Term.boxString b in
                [uu____8799] in
              [uu____8797] in
            let uu____8802 =
              let uu____8803 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8803 tt in
            (uu____8794, [bb], uu____8802) in
          FStar_SMTEncoding_Util.mkForall uu____8788 in
        (uu____8787, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Term.Assume uu____8783 in
    let uu____8814 =
      let uu____8816 =
        let uu____8817 =
          let uu____8821 =
            let uu____8822 =
              let uu____8828 =
                let uu____8829 =
                  let uu____8832 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8832) in
                FStar_SMTEncoding_Util.mkImp uu____8829 in
              ([[typing_pred]], [xx], uu____8828) in
            mkForall_fuel uu____8822 in
          (uu____8821, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8817 in
      [uu____8816] in
    uu____8782 :: uu____8814 in
  let mk_ref1 env reft_name uu____8854 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8865 =
        let uu____8869 =
          let uu____8871 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8871] in
        (reft_name, uu____8869) in
      FStar_SMTEncoding_Util.mkApp uu____8865 in
    let refb =
      let uu____8874 =
        let uu____8878 =
          let uu____8880 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8880] in
        (reft_name, uu____8878) in
      FStar_SMTEncoding_Util.mkApp uu____8874 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8884 =
      let uu____8885 =
        let uu____8889 =
          let uu____8890 =
            let uu____8896 =
              let uu____8897 =
                let uu____8900 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8900) in
              FStar_SMTEncoding_Util.mkImp uu____8897 in
            ([[typing_pred]], [xx; aa], uu____8896) in
          mkForall_fuel uu____8890 in
        (uu____8889, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Term.Assume uu____8885 in
    let uu____8915 =
      let uu____8917 =
        let uu____8918 =
          let uu____8922 =
            let uu____8923 =
              let uu____8929 =
                let uu____8930 =
                  let uu____8933 =
                    FStar_SMTEncoding_Util.mkAnd (typing_pred, typing_pred_b) in
                  let uu____8934 =
                    let uu____8935 =
                      let uu____8938 = FStar_SMTEncoding_Util.mkFreeV aa in
                      let uu____8939 = FStar_SMTEncoding_Util.mkFreeV bb in
                      (uu____8938, uu____8939) in
                    FStar_SMTEncoding_Util.mkEq uu____8935 in
                  (uu____8933, uu____8934) in
                FStar_SMTEncoding_Util.mkImp uu____8930 in
              ([[typing_pred; typing_pred_b]], [xx; aa; bb], uu____8929) in
            mkForall_fuel' (Prims.parse_int "2") uu____8923 in
          (uu____8922, (Some "ref typing is injective"), "ref_injectivity") in
        FStar_SMTEncoding_Term.Assume uu____8918 in
      [uu____8917] in
    uu____8884 :: uu____8915 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8981 =
      let uu____8982 =
        let uu____8986 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8986, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Term.Assume uu____8982 in
    [uu____8981] in
  let mk_and_interp env conj uu____8997 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9007 =
        let uu____9011 =
          let uu____9013 = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
          [uu____9013] in
        ("Valid", uu____9011) in
      FStar_SMTEncoding_Util.mkApp uu____9007 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9020 =
      let uu____9021 =
        let uu____9025 =
          let uu____9026 =
            let uu____9032 =
              let uu____9033 =
                let uu____9036 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9036, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9033 in
            ([[valid]], [aa; bb], uu____9032) in
          FStar_SMTEncoding_Util.mkForall uu____9026 in
        (uu____9025, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Term.Assume uu____9021 in
    [uu____9020] in
  let mk_or_interp env disj uu____9060 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9070 =
        let uu____9074 =
          let uu____9076 = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
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
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9099, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9096 in
            ([[valid]], [aa; bb], uu____9095) in
          FStar_SMTEncoding_Util.mkForall uu____9089 in
        (uu____9088, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Term.Assume uu____9084 in
    [uu____9083] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let valid =
      let uu____9137 =
        let uu____9141 =
          let uu____9143 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
          [uu____9143] in
        ("Valid", uu____9141) in
      FStar_SMTEncoding_Util.mkApp uu____9137 in
    let uu____9146 =
      let uu____9147 =
        let uu____9151 =
          let uu____9152 =
            let uu____9158 =
              let uu____9159 =
                let uu____9162 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9162, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9159 in
            ([[valid]], [aa; xx1; yy1], uu____9158) in
          FStar_SMTEncoding_Util.mkForall uu____9152 in
        (uu____9151, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Term.Assume uu____9147 in
    [uu____9146] in
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
      let uu____9206 =
        let uu____9210 =
          let uu____9212 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
          [uu____9212] in
        ("Valid", uu____9210) in
      FStar_SMTEncoding_Util.mkApp uu____9206 in
    let uu____9215 =
      let uu____9216 =
        let uu____9220 =
          let uu____9221 =
            let uu____9227 =
              let uu____9228 =
                let uu____9231 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9231, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9228 in
            ([[valid]], [aa; bb; xx1; yy1], uu____9227) in
          FStar_SMTEncoding_Util.mkForall uu____9221 in
        (uu____9220, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Term.Assume uu____9216 in
    [uu____9215] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9269 =
        let uu____9273 =
          let uu____9275 = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
          [uu____9275] in
        ("Valid", uu____9273) in
      FStar_SMTEncoding_Util.mkApp uu____9269 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9282 =
      let uu____9283 =
        let uu____9287 =
          let uu____9288 =
            let uu____9294 =
              let uu____9295 =
                let uu____9298 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9298, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9295 in
            ([[valid]], [aa; bb], uu____9294) in
          FStar_SMTEncoding_Util.mkForall uu____9288 in
        (uu____9287, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Term.Assume uu____9283 in
    [uu____9282] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9332 =
        let uu____9336 =
          let uu____9338 = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
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
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9361, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9358 in
            ([[valid]], [aa; bb], uu____9357) in
          FStar_SMTEncoding_Util.mkForall uu____9351 in
        (uu____9350, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Term.Assume uu____9346 in
    [uu____9345] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let valid =
      let uu____9391 =
        let uu____9395 =
          let uu____9397 = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
          [uu____9397] in
        ("Valid", uu____9395) in
      FStar_SMTEncoding_Util.mkApp uu____9391 in
    let not_valid_a =
      let uu____9401 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9401 in
    let uu____9403 =
      let uu____9404 =
        let uu____9408 =
          let uu____9409 =
            let uu____9415 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[valid]], [aa], uu____9415) in
          FStar_SMTEncoding_Util.mkForall uu____9409 in
        (uu____9408, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Term.Assume uu____9404 in
    [uu____9403] in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let valid =
      let uu____9451 =
        let uu____9455 =
          let uu____9457 = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b]) in
          [uu____9457] in
        ("Valid", uu____9455) in
      FStar_SMTEncoding_Util.mkApp uu____9451 in
    let valid_b_x =
      let uu____9461 =
        let uu____9465 =
          let uu____9467 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9467] in
        ("Valid", uu____9465) in
      FStar_SMTEncoding_Util.mkApp uu____9461 in
    let uu____9469 =
      let uu____9470 =
        let uu____9474 =
          let uu____9475 =
            let uu____9481 =
              let uu____9482 =
                let uu____9485 =
                  let uu____9486 =
                    let uu____9492 =
                      let uu____9495 =
                        let uu____9497 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9497] in
                      [uu____9495] in
                    let uu____9500 =
                      let uu____9501 =
                        let uu____9504 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9504, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9501 in
                    (uu____9492, [xx1], uu____9500) in
                  FStar_SMTEncoding_Util.mkForall uu____9486 in
                (uu____9485, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9482 in
            ([[valid]], [aa; bb], uu____9481) in
          FStar_SMTEncoding_Util.mkForall uu____9475 in
        (uu____9474, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Term.Assume uu____9470 in
    [uu____9469] in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let valid =
      let uu____9551 =
        let uu____9555 =
          let uu____9557 = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b]) in
          [uu____9557] in
        ("Valid", uu____9555) in
      FStar_SMTEncoding_Util.mkApp uu____9551 in
    let valid_b_x =
      let uu____9561 =
        let uu____9565 =
          let uu____9567 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9567] in
        ("Valid", uu____9565) in
      FStar_SMTEncoding_Util.mkApp uu____9561 in
    let uu____9569 =
      let uu____9570 =
        let uu____9574 =
          let uu____9575 =
            let uu____9581 =
              let uu____9582 =
                let uu____9585 =
                  let uu____9586 =
                    let uu____9592 =
                      let uu____9595 =
                        let uu____9597 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9597] in
                      [uu____9595] in
                    let uu____9600 =
                      let uu____9601 =
                        let uu____9604 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9604, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9601 in
                    (uu____9592, [xx1], uu____9600) in
                  FStar_SMTEncoding_Util.mkExists uu____9586 in
                (uu____9585, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9582 in
            ([[valid]], [aa; bb], uu____9581) in
          FStar_SMTEncoding_Util.mkForall uu____9575 in
        (uu____9574, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Term.Assume uu____9570 in
    [uu____9569] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9640 =
      let uu____9641 =
        let uu____9645 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9646 = varops.mk_unique "typing_range_const" in
        (uu____9645, (Some "Range_const typing"), uu____9646) in
      FStar_SMTEncoding_Term.Assume uu____9641 in
    [uu____9640] in
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
          let uu____9908 =
            FStar_Util.find_opt
              (fun uu____9926  ->
                 match uu____9926 with
                 | (l,uu____9936) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9908 with
          | None  -> []
          | Some (uu____9958,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9995 = encode_function_type_as_formula None None t env in
        match uu____9995 with
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
            let uu____10027 =
              (let uu____10028 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10028) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10027
            then
              let uu____10032 = new_term_constant_and_tok_from_lid env lid in
              match uu____10032 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10044 =
                      let uu____10045 = FStar_Syntax_Subst.compress t_norm in
                      uu____10045.FStar_Syntax_Syntax.n in
                    match uu____10044 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10050) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10067  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10070 -> [] in
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
              (let uu____10079 = prims.is lid in
               if uu____10079
               then
                 let vname = varops.new_fvar lid in
                 let uu____10084 = prims.mk lid vname in
                 match uu____10084 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10099 =
                    let uu____10105 = curried_arrow_formals_comp t_norm in
                    match uu____10105 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10116 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10116
                          then
                            let uu____10117 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___153_10118 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___153_10118.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___153_10118.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___153_10118.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___153_10118.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___153_10118.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___153_10118.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___153_10118.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___153_10118.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___153_10118.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___153_10118.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___153_10118.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___153_10118.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___153_10118.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___153_10118.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___153_10118.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___153_10118.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___153_10118.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___153_10118.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___153_10118.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___153_10118.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___153_10118.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___153_10118.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___153_10118.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10117
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10125 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10125)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10099 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10152 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10152 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10165 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___124_10189  ->
                                     match uu___124_10189 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10192 =
                                           FStar_Util.prefix vars in
                                         (match uu____10192 with
                                          | (uu____10203,(xxsym,uu____10205))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10215 =
                                                let uu____10216 =
                                                  let uu____10220 =
                                                    let uu____10221 =
                                                      let uu____10227 =
                                                        let uu____10228 =
                                                          let uu____10231 =
                                                            let uu____10232 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10232 in
                                                          (vapp, uu____10231) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10228 in
                                                      ([[vapp]], vars,
                                                        uu____10227) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10221 in
                                                  (uu____10220,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10216 in
                                              [uu____10215])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10243 =
                                           FStar_Util.prefix vars in
                                         (match uu____10243 with
                                          | (uu____10254,(xxsym,uu____10256))
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
                                              let uu____10270 =
                                                let uu____10271 =
                                                  let uu____10275 =
                                                    let uu____10276 =
                                                      let uu____10282 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10282) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10276 in
                                                  (uu____10275,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10271 in
                                              [uu____10270])
                                     | uu____10291 -> [])) in
                           let uu____10292 = encode_binders None formals env1 in
                           (match uu____10292 with
                            | (vars,guards,env',decls1,uu____10308) ->
                                let uu____10315 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10320 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10320, decls1)
                                  | Some p ->
                                      let uu____10322 = encode_formula p env' in
                                      (match uu____10322 with
                                       | (g,ds) ->
                                           let uu____10329 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10329,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10315 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10338 =
                                         let uu____10342 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10342) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10338 in
                                     let uu____10347 =
                                       let vname_decl =
                                         let uu____10352 =
                                           let uu____10358 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10363  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10358,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10352 in
                                       let uu____10368 =
                                         let env2 =
                                           let uu___154_10372 = env1 in
                                           {
                                             bindings =
                                               (uu___154_10372.bindings);
                                             depth = (uu___154_10372.depth);
                                             tcenv = (uu___154_10372.tcenv);
                                             warn = (uu___154_10372.warn);
                                             cache = (uu___154_10372.cache);
                                             nolabels =
                                               (uu___154_10372.nolabels);
                                             use_zfuel_name =
                                               (uu___154_10372.use_zfuel_name);
                                             encode_non_total_function_typ
                                           } in
                                         let uu____10373 =
                                           let uu____10374 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10374 in
                                         if uu____10373
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10368 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             FStar_SMTEncoding_Term.Assume
                                               (tok_typing,
                                                 (Some
                                                    "function token typing"),
                                                 (Prims.strcat
                                                    "function_token_typing_"
                                                    vname)) in
                                           let uu____10385 =
                                             match formals with
                                             | [] ->
                                                 let uu____10394 =
                                                   let uu____10395 =
                                                     let uu____10397 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10397 in
                                                   push_free_var env1 lid
                                                     vname uu____10395 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10394)
                                             | uu____10400 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10405 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10405 in
                                                 let name_tok_corr =
                                                   let uu____10407 =
                                                     let uu____10411 =
                                                       let uu____10412 =
                                                         let uu____10418 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10418) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10412 in
                                                     (uu____10411,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Term.Assume
                                                     uu____10407 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10385 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10347 with
                                      | (decls2,env2) ->
                                          let uu____10442 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10447 =
                                              encode_term res_t1 env' in
                                            match uu____10447 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10455 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10455,
                                                  decls) in
                                          (match uu____10442 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10463 =
                                                   let uu____10467 =
                                                     let uu____10468 =
                                                       let uu____10474 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10474) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10468 in
                                                   (uu____10467,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____10463 in
                                               let freshness =
                                                 let uu____10483 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10483
                                                 then
                                                   let uu____10486 =
                                                     let uu____10487 =
                                                       let uu____10493 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10499 =
                                                         varops.next_id () in
                                                       (vname, uu____10493,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10499) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10487 in
                                                   let uu____10501 =
                                                     let uu____10503 =
                                                       pretype_axiom vapp
                                                         vars in
                                                     [uu____10503] in
                                                   uu____10486 :: uu____10501
                                                 else [] in
                                               let g =
                                                 let uu____10507 =
                                                   let uu____10509 =
                                                     let uu____10511 =
                                                       let uu____10513 =
                                                         let uu____10515 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10515 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10513 in
                                                     FStar_List.append decls3
                                                       uu____10511 in
                                                   FStar_List.append decls2
                                                     uu____10509 in
                                                 FStar_List.append decls11
                                                   uu____10507 in
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
          let uu____10537 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10537 with
          | None  ->
              let uu____10560 = encode_free_var env x t t_norm [] in
              (match uu____10560 with
               | (decls,env1) ->
                   let uu____10575 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10575 with
                    | (n1,x',uu____10594) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10606) -> ((n1, x1), [], env)
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
          let uu____10639 = encode_free_var env lid t tt quals in
          match uu____10639 with
          | (decls,env1) ->
              let uu____10650 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10650
              then
                let uu____10654 =
                  let uu____10656 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10656 in
                (uu____10654, env1)
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
             (fun uu____10684  ->
                fun lb  ->
                  match uu____10684 with
                  | (decls,env1) ->
                      let uu____10696 =
                        let uu____10700 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10700
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10696 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10714 = FStar_Syntax_Util.head_and_args t in
    match uu____10714 with
    | (hd1,args) ->
        let uu____10740 =
          let uu____10741 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10741.FStar_Syntax_Syntax.n in
        (match uu____10740 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10745,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10758 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10773  ->
      fun quals  ->
        match uu____10773 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10822 = FStar_Util.first_N nbinders formals in
              match uu____10822 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10862  ->
                         fun uu____10863  ->
                           match (uu____10862, uu____10863) with
                           | ((formal,uu____10873),(binder,uu____10875)) ->
                               let uu____10880 =
                                 let uu____10885 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10885) in
                               FStar_Syntax_Syntax.NT uu____10880) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10890 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10904  ->
                              match uu____10904 with
                              | (x,i) ->
                                  let uu____10911 =
                                    let uu___155_10912 = x in
                                    let uu____10913 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___155_10912.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___155_10912.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10913
                                    } in
                                  (uu____10911, i))) in
                    FStar_All.pipe_right uu____10890
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10925 =
                      let uu____10927 =
                        let uu____10928 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10928.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10927 in
                    let uu____10932 =
                      let uu____10933 = FStar_Syntax_Subst.compress body in
                      let uu____10934 =
                        let uu____10935 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10935 in
                      FStar_Syntax_Syntax.extend_app_n uu____10933
                        uu____10934 in
                    uu____10932 uu____10925 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10977 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10977
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___156_10978 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___156_10978.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___156_10978.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___156_10978.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___156_10978.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___156_10978.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___156_10978.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___156_10978.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___156_10978.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___156_10978.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___156_10978.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___156_10978.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___156_10978.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___156_10978.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___156_10978.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___156_10978.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___156_10978.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___156_10978.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___156_10978.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___156_10978.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___156_10978.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___156_10978.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___156_10978.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___156_10978.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____10999 = FStar_Syntax_Util.abs_formals e in
                match uu____10999 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11048::uu____11049 ->
                         let uu____11057 =
                           let uu____11058 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11058.FStar_Syntax_Syntax.n in
                         (match uu____11057 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11085 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11085 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11111 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11111
                                   then
                                     let uu____11129 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11129 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11175  ->
                                                   fun uu____11176  ->
                                                     match (uu____11175,
                                                             uu____11176)
                                                     with
                                                     | ((x,uu____11186),
                                                        (b,uu____11188)) ->
                                                         let uu____11193 =
                                                           let uu____11198 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11198) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11193)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11200 =
                                            let uu____11211 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11211) in
                                          (uu____11200, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11246 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11246 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11298) ->
                              let uu____11303 =
                                let uu____11314 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11314 in
                              (uu____11303, true)
                          | uu____11347 when Prims.op_Negation norm1 ->
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
                          | uu____11349 ->
                              let uu____11350 =
                                let uu____11351 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11352 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11351
                                  uu____11352 in
                              failwith uu____11350)
                     | uu____11365 ->
                         let uu____11366 =
                           let uu____11367 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11367.FStar_Syntax_Syntax.n in
                         (match uu____11366 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11394 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11394 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11412 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11412 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11460 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11488 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11488
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11495 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11536  ->
                            fun lb  ->
                              match uu____11536 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11587 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11587
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11590 =
                                      let uu____11598 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11598
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11590 with
                                    | (tok,decl,env2) ->
                                        let uu____11623 =
                                          let uu____11630 =
                                            let uu____11636 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11636, tok) in
                                          uu____11630 :: toks in
                                        (uu____11623, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11495 with
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
                        | uu____11738 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11743 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11743 vars)
                            else
                              (let uu____11745 =
                                 let uu____11749 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11749) in
                               FStar_SMTEncoding_Util.mkApp uu____11745) in
                      let uu____11754 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___125_11756  ->
                                 match uu___125_11756 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11757 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11760 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11760))) in
                      if uu____11754
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11780;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11782;
                                FStar_Syntax_Syntax.lbeff = uu____11783;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11824 =
                                 FStar_Syntax_Subst.univ_var_opening uvs in
                               (match uu____11824 with
                                | (univ_subst,univ_vars1) ->
                                    let env' =
                                      let uu___159_11839 = env1 in
                                      let uu____11840 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1.tcenv univ_vars1 in
                                      {
                                        bindings = (uu___159_11839.bindings);
                                        depth = (uu___159_11839.depth);
                                        tcenv = uu____11840;
                                        warn = (uu___159_11839.warn);
                                        cache = (uu___159_11839.cache);
                                        nolabels = (uu___159_11839.nolabels);
                                        use_zfuel_name =
                                          (uu___159_11839.use_zfuel_name);
                                        encode_non_total_function_typ =
                                          (uu___159_11839.encode_non_total_function_typ)
                                      } in
                                    let t_norm1 =
                                      FStar_Syntax_Subst.subst univ_subst
                                        t_norm in
                                    let e1 =
                                      let uu____11843 =
                                        FStar_Syntax_Subst.subst univ_subst e in
                                      FStar_Syntax_Subst.compress uu____11843 in
                                    let uu____11844 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11844 with
                                     | ((binders,body,uu____11856,uu____11857),curry)
                                         ->
                                         ((let uu____11864 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11864
                                           then
                                             let uu____11865 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11866 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11865 uu____11866
                                           else ());
                                          (let uu____11868 =
                                             encode_binders None binders env' in
                                           match uu____11868 with
                                           | (vars,guards,env'1,binder_decls,uu____11884)
                                               ->
                                               let body1 =
                                                 let uu____11892 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11892
                                                 then
                                                   reify_body env'1.tcenv
                                                     body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11895 =
                                                 let uu____11900 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11900
                                                 then
                                                   let uu____11906 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11907 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11906, uu____11907)
                                                 else
                                                   (let uu____11913 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11913)) in
                                               (match uu____11895 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11927 =
                                                        let uu____11931 =
                                                          let uu____11932 =
                                                            let uu____11938 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11938) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11932 in
                                                        let uu____11944 =
                                                          let uu____11946 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11946 in
                                                        (uu____11931,
                                                          uu____11944,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Term.Assume
                                                        uu____11927 in
                                                    let uu____11948 =
                                                      let uu____11950 =
                                                        let uu____11952 =
                                                          let uu____11954 =
                                                            let uu____11956 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11956 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11954 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11952 in
                                                      FStar_List.append
                                                        decls1 uu____11950 in
                                                    (uu____11948, env1))))))
                           | uu____11959 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11978 = varops.fresh "fuel" in
                             (uu____11978, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____11981 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12020  ->
                                     fun uu____12021  ->
                                       match (uu____12020, uu____12021) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12103 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12103 in
                                           let gtok =
                                             let uu____12105 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12105 in
                                           let env3 =
                                             let uu____12107 =
                                               let uu____12109 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12109 in
                                             push_free_var env2 flid gtok
                                               uu____12107 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____11981 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12193
                                 t_norm uu____12195 =
                                 match (uu____12193, uu____12195) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12220;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12221;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12238 =
                                       FStar_Syntax_Subst.univ_var_opening
                                         uvs in
                                     (match uu____12238 with
                                      | (univ_subst,univ_vars1) ->
                                          let env' =
                                            let uu___160_12255 = env2 in
                                            let uu____12256 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env2.tcenv univ_vars1 in
                                            {
                                              bindings =
                                                (uu___160_12255.bindings);
                                              depth = (uu___160_12255.depth);
                                              tcenv = uu____12256;
                                              warn = (uu___160_12255.warn);
                                              cache = (uu___160_12255.cache);
                                              nolabels =
                                                (uu___160_12255.nolabels);
                                              use_zfuel_name =
                                                (uu___160_12255.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___160_12255.encode_non_total_function_typ)
                                            } in
                                          let t_norm1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst t_norm in
                                          let e1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst e in
                                          ((let uu____12260 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12260
                                            then
                                              let uu____12261 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12262 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12263 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12261 uu____12262
                                                uu____12263
                                            else ());
                                           (let uu____12265 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12265 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12287 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12287
                                                  then
                                                    let uu____12288 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12289 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12290 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12291 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12288 uu____12289
                                                      uu____12290 uu____12291
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12295 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12295 with
                                                  | (vars,guards,env'1,binder_decls,uu____12313)
                                                      ->
                                                      let decl_g =
                                                        let uu____12321 =
                                                          let uu____12327 =
                                                            let uu____12329 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12329 in
                                                          (g, uu____12327,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12321 in
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
                                                        let uu____12344 =
                                                          let uu____12348 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12348) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12344 in
                                                      let gsapp =
                                                        let uu____12354 =
                                                          let uu____12358 =
                                                            let uu____12360 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12360 ::
                                                              vars_tm in
                                                          (g, uu____12358) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12354 in
                                                      let gmax =
                                                        let uu____12364 =
                                                          let uu____12368 =
                                                            let uu____12370 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12370 ::
                                                              vars_tm in
                                                          (g, uu____12368) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12364 in
                                                      let body1 =
                                                        let uu____12374 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12374
                                                        then
                                                          reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12376 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12376 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12387
                                                               =
                                                               let uu____12391
                                                                 =
                                                                 let uu____12392
                                                                   =
                                                                   let uu____12400
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
                                                                    uu____12400) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12392 in
                                                               let uu____12411
                                                                 =
                                                                 let uu____12413
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12413 in
                                                               (uu____12391,
                                                                 uu____12411,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12387 in
                                                           let eqn_f =
                                                             let uu____12416
                                                               =
                                                               let uu____12420
                                                                 =
                                                                 let uu____12421
                                                                   =
                                                                   let uu____12427
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12427) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12421 in
                                                               (uu____12420,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12416 in
                                                           let eqn_g' =
                                                             let uu____12435
                                                               =
                                                               let uu____12439
                                                                 =
                                                                 let uu____12440
                                                                   =
                                                                   let uu____12446
                                                                    =
                                                                    let uu____12447
                                                                    =
                                                                    let uu____12450
                                                                    =
                                                                    let uu____12451
                                                                    =
                                                                    let uu____12455
                                                                    =
                                                                    let uu____12457
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12457
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12455) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12451 in
                                                                    (gsapp,
                                                                    uu____12450) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12447 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12446) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12440 in
                                                               (uu____12439,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12435 in
                                                           let uu____12469 =
                                                             let uu____12474
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12474
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12491)
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
                                                                    let uu____12506
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12506
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12509
                                                                    =
                                                                    let uu____12513
                                                                    =
                                                                    let uu____12514
                                                                    =
                                                                    let uu____12520
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12520) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12514 in
                                                                    (uu____12513,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Term.Assume
                                                                    uu____12509 in
                                                                 let uu____12531
                                                                   =
                                                                   let uu____12535
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12535
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12543
                                                                    =
                                                                    let uu____12545
                                                                    =
                                                                    let uu____12546
                                                                    =
                                                                    let uu____12550
                                                                    =
                                                                    let uu____12551
                                                                    =
                                                                    let uu____12557
                                                                    =
                                                                    let uu____12558
                                                                    =
                                                                    let uu____12561
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12561,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12558 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12557) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12551 in
                                                                    (uu____12550,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12546 in
                                                                    [uu____12545] in
                                                                    (d3,
                                                                    uu____12543) in
                                                                 (match uu____12531
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12469
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
                               let uu____12596 =
                                 let uu____12603 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12635  ->
                                      fun uu____12636  ->
                                        match (uu____12635, uu____12636) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12712 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12712 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12603 in
                               (match uu____12596 with
                                | (decls2,eqns,env01) ->
                                    let uu____12752 =
                                      let isDeclFun uu___126_12760 =
                                        match uu___126_12760 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12761 -> true
                                        | uu____12767 -> false in
                                      let uu____12768 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12768
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12752 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12795 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12795
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
      (let uu____12828 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____12828
       then
         let uu____12829 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
           uu____12829
       else ());
      (let nm =
         let uu____12832 = FStar_Syntax_Util.lid_of_sigelt se in
         match uu____12832 with | None  -> "" | Some l -> l.FStar_Ident.str in
       let uu____12835 = encode_sigelt' env se in
       match uu____12835 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12844 =
                  let uu____12846 =
                    let uu____12847 = FStar_Util.format1 "<Skipped %s/>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12847 in
                  [uu____12846] in
                (uu____12844, e)
            | uu____12849 ->
                let uu____12850 =
                  let uu____12852 =
                    let uu____12854 =
                      let uu____12855 =
                        FStar_Util.format1 "<Start encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12855 in
                    uu____12854 :: g in
                  let uu____12856 =
                    let uu____12858 =
                      let uu____12859 =
                        FStar_Util.format1 "</end encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12859 in
                    [uu____12858] in
                  FStar_List.append uu____12852 uu____12856 in
                (uu____12850, e)))
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12867 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12876 =
            let uu____12877 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12877 Prims.op_Negation in
          if uu____12876
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12897 ->
                   let uu____12898 =
                     let uu____12901 =
                       let uu____12902 =
                         let uu____12917 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12917) in
                       FStar_Syntax_Syntax.Tm_abs uu____12902 in
                     FStar_Syntax_Syntax.mk uu____12901 in
                   uu____12898 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____12970 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____12970 with
               | (aname,atok,env2) ->
                   let uu____12980 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____12980 with
                    | (formals,uu____12990) ->
                        let uu____12997 =
                          let uu____13000 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13000 env2 in
                        (match uu____12997 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13008 =
                                 let uu____13009 =
                                   let uu____13015 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13023  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13015,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13009 in
                               [uu____13008;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13030 =
                               let aux uu____13059 uu____13060 =
                                 match (uu____13059, uu____13060) with
                                 | ((bv,uu____13087),(env3,acc_sorts,acc)) ->
                                     let uu____13108 = gen_term_var env3 bv in
                                     (match uu____13108 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13030 with
                              | (uu____13146,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13160 =
                                      let uu____13164 =
                                        let uu____13165 =
                                          let uu____13171 =
                                            let uu____13172 =
                                              let uu____13175 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13175) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13172 in
                                          ([[app]], xs_sorts, uu____13171) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13165 in
                                      (uu____13164, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Term.Assume uu____13160 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13187 =
                                      let uu____13191 =
                                        let uu____13192 =
                                          let uu____13198 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13198) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13192 in
                                      (uu____13191,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Term.Assume uu____13187 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13208 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13208 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____13224,uu____13225,uu____13226) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13229 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13229 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13240,t,quals) ->
          let will_encode_definition =
            let uu____13246 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___127_13248  ->
                      match uu___127_13248 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13251 -> false)) in
            Prims.op_Negation uu____13246 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13257 = encode_top_level_val env fv t quals in
             match uu____13257 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13269 =
                   let uu____13271 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13271 in
                 (uu____13269, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____13276) ->
          let uu____13279 = encode_formula f env in
          (match uu____13279 with
           | (f1,decls) ->
               let g =
                 let uu____13288 =
                   let uu____13289 =
                     let uu____13293 =
                       let uu____13295 =
                         let uu____13296 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13296 in
                       Some uu____13295 in
                     let uu____13297 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13293, uu____13297) in
                   FStar_SMTEncoding_Term.Assume uu____13289 in
                 [uu____13288] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13301,quals,uu____13303) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13311 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13318 =
                       let uu____13323 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13323.FStar_Syntax_Syntax.fv_name in
                     uu____13318.FStar_Syntax_Syntax.v in
                   let uu____13327 =
                     let uu____13328 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13328 in
                   if uu____13327
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
                     let uu____13347 = encode_sigelt' env1 val_decl in
                     match uu____13347 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13311 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13364,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13366;
                          FStar_Syntax_Syntax.lbtyp = uu____13367;
                          FStar_Syntax_Syntax.lbeff = uu____13368;
                          FStar_Syntax_Syntax.lbdef = uu____13369;_}::[]),uu____13370,uu____13371,uu____13372)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13388 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13388 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let valid_b2t_x =
                 let uu____13406 =
                   let uu____13410 =
                     let uu____13412 =
                       FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
                     [uu____13412] in
                   ("Valid", uu____13410) in
                 FStar_SMTEncoding_Util.mkApp uu____13406 in
               let decls =
                 let uu____13417 =
                   let uu____13419 =
                     let uu____13420 =
                       let uu____13424 =
                         let uu____13425 =
                           let uu____13431 =
                             let uu____13432 =
                               let uu____13435 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13435) in
                             FStar_SMTEncoding_Util.mkEq uu____13432 in
                           ([[valid_b2t_x]], [xx], uu____13431) in
                         FStar_SMTEncoding_Util.mkForall uu____13425 in
                       (uu____13424, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Term.Assume uu____13420 in
                   [uu____13419] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13417 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let
          (uu____13452,uu____13453,quals,uu____13455) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___128_13463  ->
                  match uu___128_13463 with
                  | FStar_Syntax_Syntax.Discriminator uu____13464 -> true
                  | uu____13465 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13467,lids,quals,uu____13470) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13479 =
                     let uu____13480 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13480.FStar_Ident.idText in
                   uu____13479 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___129_13482  ->
                     match uu___129_13482 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13483 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13486,quals,uu____13488) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___130_13500  ->
                  match uu___130_13500 with
                  | FStar_Syntax_Syntax.Projector uu____13501 -> true
                  | uu____13504 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13511 = try_lookup_free_var env l in
          (match uu____13511 with
           | Some uu____13515 -> ([], env)
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
          ((is_rec,bindings),uu____13524,quals,uu____13526) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13540,uu____13541) ->
          let uu____13548 = encode_signature env ses in
          (match uu____13548 with
           | (g,env1) ->
               let uu____13558 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___131_13568  ->
                         match uu___131_13568 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13569,Some "inversion axiom",uu____13570)
                             -> false
                         | uu____13572 -> true)) in
               (match uu____13558 with
                | (g',inversions) ->
                    let uu____13581 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___132_13591  ->
                              match uu___132_13591 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13592 ->
                                  true
                              | uu____13598 -> false)) in
                    (match uu____13581 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13609,tps,k,uu____13612,datas,quals) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___133_13623  ->
                    match uu___133_13623 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13624 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13631 = c in
              match uu____13631 with
              | (name,args,uu____13635,uu____13636,uu____13637) ->
                  let uu____13640 =
                    let uu____13641 =
                      let uu____13647 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13654  ->
                                match uu____13654 with
                                | (uu____13658,sort,uu____13660) -> sort)) in
                      (name, uu____13647, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13641 in
                  [uu____13640]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13678 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13681 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13681 FStar_Option.isNone)) in
            if uu____13678
            then []
            else
              (let uu____13698 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13698 with
               | (xxsym,xx) ->
                   let uu____13704 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13715  ->
                             fun l  ->
                               match uu____13715 with
                               | (out,decls) ->
                                   let uu____13727 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13727 with
                                    | (uu____13733,data_t) ->
                                        let uu____13735 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13735 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13764 =
                                                 let uu____13765 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13765.FStar_Syntax_Syntax.n in
                                               match uu____13764 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13773,indices) ->
                                                   indices
                                               | uu____13789 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13801  ->
                                                         match uu____13801
                                                         with
                                                         | (x,uu____13805) ->
                                                             let uu____13806
                                                               =
                                                               let uu____13807
                                                                 =
                                                                 let uu____13811
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13811,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13807 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13806)
                                                    env) in
                                             let uu____13813 =
                                               encode_args indices env1 in
                                             (match uu____13813 with
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
                                                      let uu____13833 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13841
                                                                 =
                                                                 let uu____13844
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13844,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13841)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13833
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13846 =
                                                      let uu____13847 =
                                                        let uu____13850 =
                                                          let uu____13851 =
                                                            let uu____13854 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13854,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13851 in
                                                        (out, uu____13850) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13847 in
                                                    (uu____13846,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13704 with
                    | (data_ax,decls) ->
                        let uu____13862 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13862 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13873 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13873 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13876 =
                                 let uu____13880 =
                                   let uu____13881 =
                                     let uu____13887 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13895 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13887,
                                       uu____13895) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13881 in
                                 let uu____13903 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13880, (Some "inversion axiom"),
                                   uu____13903) in
                               FStar_SMTEncoding_Term.Assume uu____13876 in
                             let pattern_guarded_inversion =
                               let uu____13907 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13907
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13915 =
                                   let uu____13916 =
                                     let uu____13920 =
                                       let uu____13921 =
                                         let uu____13927 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13935 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13927, uu____13935) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13921 in
                                     let uu____13943 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13920, (Some "inversion axiom"),
                                       uu____13943) in
                                   FStar_SMTEncoding_Term.Assume uu____13916 in
                                 [uu____13915]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13946 =
            let uu____13954 =
              let uu____13955 = FStar_Syntax_Subst.compress k in
              uu____13955.FStar_Syntax_Syntax.n in
            match uu____13954 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13984 -> (tps, k) in
          (match uu____13946 with
           | (formals,res) ->
               let uu____13999 = FStar_Syntax_Subst.open_term formals res in
               (match uu____13999 with
                | (formals1,res1) ->
                    let uu____14006 = encode_binders None formals1 env in
                    (match uu____14006 with
                     | (vars,guards,env',binder_decls,uu____14021) ->
                         let uu____14028 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14028 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14041 =
                                  let uu____14045 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14045) in
                                FStar_SMTEncoding_Util.mkApp uu____14041 in
                              let uu____14050 =
                                let tname_decl =
                                  let uu____14056 =
                                    let uu____14057 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14072  ->
                                              match uu____14072 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14080 = varops.next_id () in
                                    (tname, uu____14057,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14080, false) in
                                  constructor_or_logic_type_decl uu____14056 in
                                let uu____14085 =
                                  match vars with
                                  | [] ->
                                      let uu____14092 =
                                        let uu____14093 =
                                          let uu____14095 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14095 in
                                        push_free_var env1 t tname
                                          uu____14093 in
                                      ([], uu____14092)
                                  | uu____14099 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14105 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14105 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14114 =
                                          let uu____14118 =
                                            let uu____14119 =
                                              let uu____14127 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14127) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14119 in
                                          (uu____14118,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____14114 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14085 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14050 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14150 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14150 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14164 =
                                               let uu____14165 =
                                                 let uu____14169 =
                                                   let uu____14170 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14170 in
                                                 (uu____14169,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14165 in
                                             [uu____14164]
                                           else [] in
                                         let uu____14173 =
                                           let uu____14175 =
                                             let uu____14177 =
                                               let uu____14178 =
                                                 let uu____14182 =
                                                   let uu____14183 =
                                                     let uu____14189 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14189) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14183 in
                                                 (uu____14182, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14178 in
                                             [uu____14177] in
                                           FStar_List.append karr uu____14175 in
                                         FStar_List.append decls1 uu____14173 in
                                   let aux =
                                     let uu____14198 =
                                       let uu____14200 =
                                         inversion_axioms tapp vars in
                                       let uu____14202 =
                                         let uu____14204 =
                                           pretype_axiom tapp vars in
                                         [uu____14204] in
                                       FStar_List.append uu____14200
                                         uu____14202 in
                                     FStar_List.append kindingAx uu____14198 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14209,uu____14210,uu____14211,uu____14212,uu____14213,uu____14214)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14221,t,uu____14223,n_tps,quals,uu____14226) ->
          let uu____14231 = new_term_constant_and_tok_from_lid env d in
          (match uu____14231 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14242 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14242 with
                | (formals,t_res) ->
                    let uu____14264 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14264 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14273 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14273 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14311 =
                                            mk_term_projector_name d x in
                                          (uu____14311,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14313 =
                                  let uu____14323 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14323, true) in
                                FStar_All.pipe_right uu____14313
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
                              let uu____14345 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14345 with
                               | (tok_typing,decls3) ->
                                   let uu____14352 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14352 with
                                    | (vars',guards',env'',decls_formals,uu____14367)
                                        ->
                                        let uu____14374 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14374 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14393 ->
                                                   let uu____14397 =
                                                     let uu____14398 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14398 in
                                                   [uu____14397] in
                                             let encode_elim uu____14405 =
                                               let uu____14406 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14406 with
                                               | (head1,args) ->
                                                   let uu____14435 =
                                                     let uu____14436 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14436.FStar_Syntax_Syntax.n in
                                                   (match uu____14435 with
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
                                                        let uu____14454 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14454
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
                                                                 | uu____14480
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14488
                                                                    =
                                                                    let uu____14489
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14489 in
                                                                    if
                                                                    uu____14488
                                                                    then
                                                                    let uu____14496
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14496]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14498
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14511
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14511
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14533
                                                                    =
                                                                    let uu____14537
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14537 in
                                                                    (match uu____14533
                                                                    with
                                                                    | 
                                                                    (uu____14544,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14550
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14550
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14552
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14552
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
                                                             (match uu____14498
                                                              with
                                                              | (uu____14560,arg_vars,elim_eqns_or_guards,uu____14563)
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
                                                                    let uu____14582
                                                                    =
                                                                    let uu____14586
                                                                    =
                                                                    let uu____14587
                                                                    =
                                                                    let uu____14593
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14599
                                                                    =
                                                                    let uu____14600
                                                                    =
                                                                    let uu____14603
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14603) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14600 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14593,
                                                                    uu____14599) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14587 in
                                                                    (uu____14586,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14582 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14616
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14616,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14618
                                                                    =
                                                                    let uu____14622
                                                                    =
                                                                    let uu____14623
                                                                    =
                                                                    let uu____14629
                                                                    =
                                                                    let uu____14632
                                                                    =
                                                                    let uu____14634
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14634] in
                                                                    [uu____14632] in
                                                                    let uu____14637
                                                                    =
                                                                    let uu____14638
                                                                    =
                                                                    let uu____14641
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14642
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14641,
                                                                    uu____14642) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14638 in
                                                                    (uu____14629,
                                                                    [x],
                                                                    uu____14637) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14623 in
                                                                    let uu____14652
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14622,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14652) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14618
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14657
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
                                                                    (let uu____14672
                                                                    =
                                                                    let uu____14673
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14673
                                                                    dapp1 in
                                                                    [uu____14672]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14657
                                                                    FStar_List.flatten in
                                                                    let uu____14677
                                                                    =
                                                                    let uu____14681
                                                                    =
                                                                    let uu____14682
                                                                    =
                                                                    let uu____14688
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14694
                                                                    =
                                                                    let uu____14695
                                                                    =
                                                                    let uu____14698
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14698) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14695 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14688,
                                                                    uu____14694) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14682 in
                                                                    (uu____14681,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14677) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14708 ->
                                                        ((let uu____14710 =
                                                            let uu____14711 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14712 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14711
                                                              uu____14712 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14710);
                                                         ([], []))) in
                                             let uu____14715 = encode_elim () in
                                             (match uu____14715 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14727 =
                                                      let uu____14729 =
                                                        let uu____14731 =
                                                          let uu____14733 =
                                                            let uu____14735 =
                                                              let uu____14736
                                                                =
                                                                let uu____14742
                                                                  =
                                                                  let uu____14744
                                                                    =
                                                                    let uu____14745
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14745 in
                                                                  Some
                                                                    uu____14744 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14742) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14736 in
                                                            [uu____14735] in
                                                          let uu____14748 =
                                                            let uu____14750 =
                                                              let uu____14752
                                                                =
                                                                let uu____14754
                                                                  =
                                                                  let uu____14756
                                                                    =
                                                                    let uu____14758
                                                                    =
                                                                    let uu____14760
                                                                    =
                                                                    let uu____14761
                                                                    =
                                                                    let uu____14765
                                                                    =
                                                                    let uu____14766
                                                                    =
                                                                    let uu____14772
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14772) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14766 in
                                                                    (uu____14765,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14761 in
                                                                    let uu____14779
                                                                    =
                                                                    let uu____14781
                                                                    =
                                                                    let uu____14782
                                                                    =
                                                                    let uu____14786
                                                                    =
                                                                    let uu____14787
                                                                    =
                                                                    let uu____14793
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14799
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14793,
                                                                    uu____14799) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14787 in
                                                                    (uu____14786,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14782 in
                                                                    [uu____14781] in
                                                                    uu____14760
                                                                    ::
                                                                    uu____14779 in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14758 in
                                                                  FStar_List.append
                                                                    uu____14756
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14754 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14752 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14750 in
                                                          FStar_List.append
                                                            uu____14733
                                                            uu____14748 in
                                                        FStar_List.append
                                                          decls3 uu____14731 in
                                                      FStar_List.append
                                                        decls2 uu____14729 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14727 in
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
           (fun uu____14820  ->
              fun se  ->
                match uu____14820 with
                | (g,env1) ->
                    let uu____14832 = encode_sigelt env1 se in
                    (match uu____14832 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14868 =
        match uu____14868 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14886 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14891 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14891
                   then
                     let uu____14892 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14893 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14894 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14892 uu____14893 uu____14894
                   else ());
                  (let uu____14896 = encode_term t1 env1 in
                   match uu____14896 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14906 =
                         let uu____14910 =
                           let uu____14911 =
                             let uu____14912 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____14912
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____14911 in
                         new_term_constant_from_string env1 x uu____14910 in
                       (match uu____14906 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____14923 = FStar_Options.log_queries () in
                              if uu____14923
                              then
                                let uu____14925 =
                                  let uu____14926 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____14927 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____14928 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14926 uu____14927 uu____14928 in
                                Some uu____14925
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14939,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____14948 = encode_free_var env1 fv t t_norm [] in
                 (match uu____14948 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____14967 = encode_sigelt env1 se in
                 (match uu____14967 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____14977 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____14977 with | (uu____14989,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15034  ->
            match uu____15034 with
            | (l,uu____15041,uu____15042) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15063  ->
            match uu____15063 with
            | (l,uu____15071,uu____15072) ->
                let uu____15077 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____15078 =
                  let uu____15080 =
                    let uu____15081 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15081 in
                  [uu____15080] in
                uu____15077 :: uu____15078)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15092 =
      let uu____15094 =
        let uu____15095 = FStar_Util.smap_create (Prims.parse_int "100") in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15095;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true
        } in
      [uu____15094] in
    FStar_ST.write last_env uu____15092
let get_env: FStar_TypeChecker_Env.env -> env_t =
  fun tcenv  ->
    let uu____15113 = FStar_ST.read last_env in
    match uu____15113 with
    | [] -> failwith "No env; call init first!"
    | e::uu____15119 ->
        let uu___161_15121 = e in
        {
          bindings = (uu___161_15121.bindings);
          depth = (uu___161_15121.depth);
          tcenv;
          warn = (uu___161_15121.warn);
          cache = (uu___161_15121.cache);
          nolabels = (uu___161_15121.nolabels);
          use_zfuel_name = (uu___161_15121.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___161_15121.encode_non_total_function_typ)
        }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15125 = FStar_ST.read last_env in
    match uu____15125 with
    | [] -> failwith "Empty env stack"
    | uu____15130::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15138  ->
    let uu____15139 = FStar_ST.read last_env in
    match uu____15139 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___162_15160 = hd1 in
          {
            bindings = (uu___162_15160.bindings);
            depth = (uu___162_15160.depth);
            tcenv = (uu___162_15160.tcenv);
            warn = (uu___162_15160.warn);
            cache = refs;
            nolabels = (uu___162_15160.nolabels);
            use_zfuel_name = (uu___162_15160.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_15160.encode_non_total_function_typ)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15166  ->
    let uu____15167 = FStar_ST.read last_env in
    match uu____15167 with
    | [] -> failwith "Popping an empty stack"
    | uu____15172::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15180  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15183  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15186  ->
    let uu____15187 = FStar_ST.read last_env in
    match uu____15187 with
    | hd1::uu____15193::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15199 -> failwith "Impossible"
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
        let uu____15244 = FStar_Options.log_queries () in
        if uu____15244
        then
          let uu____15246 =
            let uu____15247 =
              let uu____15248 =
                let uu____15249 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15249 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15248 in
            FStar_SMTEncoding_Term.Caption uu____15247 in
          uu____15246 :: decls
        else decls in
      let env = get_env tcenv in
      let uu____15256 = encode_sigelt env se in
      match uu____15256 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15262 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15262))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15273 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15273
       then
         let uu____15274 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15274
       else ());
      (let env = get_env tcenv in
       let uu____15279 =
         encode_signature
           (let uu___163_15283 = env in
            {
              bindings = (uu___163_15283.bindings);
              depth = (uu___163_15283.depth);
              tcenv = (uu___163_15283.tcenv);
              warn = false;
              cache = (uu___163_15283.cache);
              nolabels = (uu___163_15283.nolabels);
              use_zfuel_name = (uu___163_15283.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___163_15283.encode_non_total_function_typ)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15279 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15295 = FStar_Options.log_queries () in
             if uu____15295
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___164_15300 = env1 in
               {
                 bindings = (uu___164_15300.bindings);
                 depth = (uu___164_15300.depth);
                 tcenv = (uu___164_15300.tcenv);
                 warn = true;
                 cache = (uu___164_15300.cache);
                 nolabels = (uu___164_15300.nolabels);
                 use_zfuel_name = (uu___164_15300.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___164_15300.encode_non_total_function_typ)
               });
            (let uu____15302 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15302
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
        (let uu____15337 =
           let uu____15338 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15338.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15337);
        (let env = get_env tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15346 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15367 = aux rest in
                 (match uu____15367 with
                  | (out,rest1) ->
                      let t =
                        let uu____15385 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15385 with
                        | Some uu____15389 ->
                            let uu____15390 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15390
                              x.FStar_Syntax_Syntax.sort
                        | uu____15391 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15394 =
                        let uu____15396 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___165_15397 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___165_15397.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___165_15397.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15396 :: out in
                      (uu____15394, rest1))
             | uu____15400 -> ([], bindings1) in
           let uu____15404 = aux bindings in
           match uu____15404 with
           | (closing,bindings1) ->
               let uu____15418 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15418, bindings1) in
         match uu____15346 with
         | (q1,bindings1) ->
             let uu____15431 =
               let uu____15434 =
                 FStar_List.filter
                   (fun uu___134_15436  ->
                      match uu___134_15436 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15437 ->
                          false
                      | uu____15441 -> true) bindings1 in
               encode_env_bindings env uu____15434 in
             (match uu____15431 with
              | (env_decls,env1) ->
                  ((let uu____15452 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15452
                    then
                      let uu____15453 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15453
                    else ());
                   (let uu____15455 = encode_formula q1 env1 in
                    match uu____15455 with
                    | (phi,qdecls) ->
                        let uu____15467 =
                          let uu____15470 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15470 phi in
                        (match uu____15467 with
                         | (labels,phi1) ->
                             let uu____15480 = encode_labels labels in
                             (match uu____15480 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15501 =
                                      let uu____15505 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15506 =
                                        varops.mk_unique "@query" in
                                      (uu____15505, (Some "query"),
                                        uu____15506) in
                                    FStar_SMTEncoding_Term.Assume uu____15501 in
                                  let suffix =
                                    let uu____15510 =
                                      let uu____15512 =
                                        let uu____15514 =
                                          FStar_Options.print_z3_statistics
                                            () in
                                        if uu____15514
                                        then
                                          [FStar_SMTEncoding_Term.PrintStats]
                                        else [] in
                                      FStar_List.append uu____15512
                                        [FStar_SMTEncoding_Term.Echo "Done!"] in
                                    FStar_List.append label_suffix
                                      uu____15510 in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env = get_env tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15527 = encode_formula q env in
       match uu____15527 with
       | (f,uu____15531) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15533) -> true
             | uu____15536 -> false)))