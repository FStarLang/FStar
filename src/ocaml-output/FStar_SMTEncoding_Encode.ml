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
           let module_name =
             let uu____2495 = FStar_TypeChecker_Env.current_module env.tcenv in
             FStar_All.pipe_right uu____2495 FStar_Ident.string_of_lid in
           let uu____2496 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2496 with
            | (binders1,res) ->
                let uu____2503 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2503
                then
                  let uu____2506 = encode_binders None binders1 env in
                  (match uu____2506 with
                   | (vars,guards,env',decls,uu____2521) ->
                       let fsym =
                         let uu____2531 = varops.fresh "f" in
                         (uu____2531, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2534 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___144_2538 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___144_2538.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___144_2538.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___144_2538.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___144_2538.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___144_2538.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___144_2538.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___144_2538.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___144_2538.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___144_2538.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___144_2538.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___144_2538.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___144_2538.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___144_2538.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___144_2538.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___144_2538.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___144_2538.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___144_2538.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___144_2538.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___144_2538.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___144_2538.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___144_2538.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___144_2538.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___144_2538.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2534 with
                        | (pre_opt,res_t) ->
                            let uu____2545 =
                              encode_term_pred None res_t env' app in
                            (match uu____2545 with
                             | (res_pred,decls') ->
                                 let uu____2552 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2559 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2559, [])
                                   | Some pre ->
                                       let uu____2562 =
                                         encode_formula pre env' in
                                       (match uu____2562 with
                                        | (guard,decls0) ->
                                            let uu____2570 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2570, decls0)) in
                                 (match uu____2552 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2578 =
                                          let uu____2584 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2584) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2578 in
                                      let cvars =
                                        let uu____2594 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2594
                                          (FStar_List.filter
                                             (fun uu____2600  ->
                                                match uu____2600 with
                                                | (x,uu____2604) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2615 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2615 with
                                       | Some (t',sorts,uu____2631) ->
                                           let uu____2641 =
                                             let uu____2642 =
                                               let uu____2646 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               (t', uu____2646) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2642 in
                                           (uu____2641, [])
                                       | None  ->
                                           let tsym =
                                             let uu____2662 =
                                               let uu____2663 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2663 in
                                             varops.mk_unique uu____2662 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2670 =
                                               FStar_Options.log_queries () in
                                             if uu____2670
                                             then
                                               let uu____2672 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2672
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2678 =
                                               let uu____2682 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2682) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2678 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____2690 =
                                               let uu____2694 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2694, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2690 in
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
                                             let uu____2707 =
                                               let uu____2711 =
                                                 let uu____2712 =
                                                   let uu____2718 =
                                                     let uu____2719 =
                                                       let uu____2722 =
                                                         let uu____2723 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2723 in
                                                       (f_has_t, uu____2722) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2719 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2718) in
                                                 mkForall_fuel uu____2712 in
                                               (uu____2711,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2707 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____2736 =
                                               let uu____2740 =
                                                 let uu____2741 =
                                                   let uu____2747 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2747) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2741 in
                                               (uu____2740, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2736 in
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
                     let uu____2778 =
                       let uu____2782 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____2782, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Term.Assume uu____2778 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____2791 =
                       let uu____2795 =
                         let uu____2796 =
                           let uu____2802 =
                             let uu____2803 =
                               let uu____2806 =
                                 let uu____2807 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2807 in
                               (f_has_t, uu____2806) in
                             FStar_SMTEncoding_Util.mkImp uu____2803 in
                           ([[f_has_t]], [fsym], uu____2802) in
                         mkForall_fuel uu____2796 in
                       (uu____2795, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Term.Assume uu____2791 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2821 ->
           let uu____2826 =
             let uu____2829 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2829 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2834;
                 FStar_Syntax_Syntax.pos = uu____2835;
                 FStar_Syntax_Syntax.vars = uu____2836;_} ->
                 let uu____2843 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2843 with
                  | (b,f1) ->
                      let uu____2857 =
                        let uu____2858 = FStar_List.hd b in
                        Prims.fst uu____2858 in
                      (uu____2857, f1))
             | uu____2863 -> failwith "impossible" in
           (match uu____2826 with
            | (x,f) ->
                let uu____2870 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____2870 with
                 | (base_t,decls) ->
                     let uu____2877 = gen_term_var env x in
                     (match uu____2877 with
                      | (x1,xtm,env') ->
                          let uu____2886 = encode_formula f env' in
                          (match uu____2886 with
                           | (refinement,decls') ->
                               let uu____2893 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____2893 with
                                | (fsym,fterm) ->
                                    let encoding =
                                      let uu____2901 =
                                        let uu____2904 =
                                          FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                            (Some fterm) xtm base_t in
                                        (uu____2904, refinement) in
                                      FStar_SMTEncoding_Util.mkAnd uu____2901 in
                                    let cvars =
                                      let uu____2909 =
                                        FStar_SMTEncoding_Term.free_variables
                                          encoding in
                                      FStar_All.pipe_right uu____2909
                                        (FStar_List.filter
                                           (fun uu____2915  ->
                                              match uu____2915 with
                                              | (y,uu____2919) ->
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
                                    let uu____2938 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2938 with
                                     | Some (t1,uu____2953,uu____2954) ->
                                         let uu____2964 =
                                           let uu____2965 =
                                             let uu____2969 =
                                               FStar_All.pipe_right cvars
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             (t1, uu____2969) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2965 in
                                         (uu____2964, [])
                                     | None  ->
                                         let module_name =
                                           let uu____2985 =
                                             FStar_TypeChecker_Env.current_module
                                               env.tcenv in
                                           FStar_All.pipe_right uu____2985
                                             FStar_Ident.string_of_lid in
                                         let tsym =
                                           let uu____2987 =
                                             let uu____2988 =
                                               let uu____2989 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____2989 in
                                             Prims.strcat module_name
                                               uu____2988 in
                                           varops.mk_unique uu____2987 in
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
                                             let uu____3016 =
                                               let uu____3017 =
                                                 let uu____3023 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars,
                                                   uu____3023) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3017 in
                                             (uu____3016,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3012 in
                                         let t_kinding =
                                           let uu____3033 =
                                             let uu____3037 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars,
                                                   t_has_kind) in
                                             (uu____3037,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3033 in
                                         let t_interp =
                                           let uu____3047 =
                                             let uu____3051 =
                                               let uu____3052 =
                                                 let uu____3058 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars), uu____3058) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3052 in
                                             let uu____3070 =
                                               let uu____3072 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3072 in
                                             (uu____3051, uu____3070,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3047 in
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
             let uu____3100 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3100 in
           let uu____3104 = encode_term_pred None k env ttm in
           (match uu____3104 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3112 =
                    let uu____3116 =
                      let uu____3117 =
                        let uu____3118 =
                          let uu____3119 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3119 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3118 in
                      varops.mk_unique uu____3117 in
                    (t_has_k, (Some "Uvar typing"), uu____3116) in
                  FStar_SMTEncoding_Term.Assume uu____3112 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3125 ->
           let uu____3135 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3135 with
            | (head1,args_e) ->
                let uu____3163 =
                  let uu____3171 =
                    let uu____3172 = FStar_Syntax_Subst.compress head1 in
                    uu____3172.FStar_Syntax_Syntax.n in
                  (uu____3171, args_e) in
                (match uu____3163 with
                 | (uu____3182,uu____3183) when head_redex env head1 ->
                     let uu____3194 = whnf env t in
                     encode_term uu____3194 env
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
                     let uu____3268 = encode_term v1 env in
                     (match uu____3268 with
                      | (v11,decls1) ->
                          let uu____3275 = encode_term v2 env in
                          (match uu____3275 with
                           | (v21,decls2) ->
                               let uu____3282 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3282,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3284) ->
                     let e0 =
                       let uu____3298 =
                         let uu____3301 =
                           let uu____3302 =
                             let uu____3312 =
                               let uu____3318 = FStar_List.hd args_e in
                               [uu____3318] in
                             (head1, uu____3312) in
                           FStar_Syntax_Syntax.Tm_app uu____3302 in
                         FStar_Syntax_Syntax.mk uu____3301 in
                       uu____3298 None head1.FStar_Syntax_Syntax.pos in
                     ((let uu____3351 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3351
                       then
                         let uu____3352 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Trying to normalize %s\n"
                           uu____3352
                       else ());
                      (let e01 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Reify;
                           FStar_TypeChecker_Normalize.Eager_unfolding;
                           FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                           env.tcenv e0 in
                       (let uu____3356 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify") in
                        if uu____3356
                        then
                          let uu____3357 =
                            FStar_Syntax_Print.term_to_string e01 in
                          FStar_Util.print1 "Result of normalization %s\n"
                            uu____3357
                        else ());
                       (let e02 =
                          let uu____3360 =
                            let uu____3361 =
                              let uu____3362 =
                                FStar_Syntax_Subst.compress e01 in
                              uu____3362.FStar_Syntax_Syntax.n in
                            match uu____3361 with
                            | FStar_Syntax_Syntax.Tm_app uu____3365 -> false
                            | uu____3375 -> true in
                          if uu____3360
                          then e01
                          else
                            (let uu____3377 =
                               FStar_Syntax_Util.head_and_args e01 in
                             match uu____3377 with
                             | (head2,args) ->
                                 let uu____3403 =
                                   let uu____3404 =
                                     let uu____3405 =
                                       FStar_Syntax_Subst.compress head2 in
                                     uu____3405.FStar_Syntax_Syntax.n in
                                   match uu____3404 with
                                   | FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_reify ) -> true
                                   | uu____3408 -> false in
                                 if uu____3403
                                 then
                                   (match args with
                                    | x::[] -> Prims.fst x
                                    | uu____3424 ->
                                        failwith
                                          "Impossible : Reify applied to multiple arguments after normalization.")
                                 else e01) in
                        let e =
                          match args_e with
                          | uu____3432::[] -> e02
                          | uu____3445 ->
                              let uu____3451 =
                                let uu____3454 =
                                  let uu____3455 =
                                    let uu____3465 = FStar_List.tl args_e in
                                    (e02, uu____3465) in
                                  FStar_Syntax_Syntax.Tm_app uu____3455 in
                                FStar_Syntax_Syntax.mk uu____3454 in
                              uu____3451 None t0.FStar_Syntax_Syntax.pos in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3488),(arg,uu____3490)::[]) -> encode_term arg env
                 | uu____3508 ->
                     let uu____3516 = encode_args args_e env in
                     (match uu____3516 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3549 = encode_term head1 env in
                            match uu____3549 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3588 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3588 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3630  ->
                                                 fun uu____3631  ->
                                                   match (uu____3630,
                                                           uu____3631)
                                                   with
                                                   | ((bv,uu____3645),
                                                      (a,uu____3647)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3661 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3661
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3666 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3666 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3676 =
                                                   let uu____3680 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3685 =
                                                     let uu____3686 =
                                                       let uu____3687 =
                                                         let uu____3688 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3688 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3687 in
                                                     varops.mk_unique
                                                       uu____3686 in
                                                   (uu____3680,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3685) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3676 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3705 = lookup_free_var_sym env fv in
                            match uu____3705 with
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
                                let uu____3743 =
                                  let uu____3744 =
                                    let uu____3747 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3747 Prims.fst in
                                  FStar_All.pipe_right uu____3744 Prims.snd in
                                Some uu____3743
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3766,(FStar_Util.Inl t1,uu____3768),uu____3769)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3807,(FStar_Util.Inr c,uu____3809),uu____3810)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3848 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3868 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3868 in
                               let uu____3869 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3869 with
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
                                     | uu____3894 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3939 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3939 with
            | (bs1,body1,opening) ->
                let fallback uu____3954 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3959 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3959, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3970 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3970
                  | FStar_Util.Inr (eff,uu____3972) ->
                      let uu____3978 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3978 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body = reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4023 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___145_4024 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___145_4024.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___145_4024.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___145_4024.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___145_4024.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___145_4024.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___145_4024.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___145_4024.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___145_4024.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___145_4024.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___145_4024.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___145_4024.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___145_4024.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___145_4024.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___145_4024.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___145_4024.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___145_4024.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___145_4024.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___145_4024.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___145_4024.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___145_4024.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___145_4024.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___145_4024.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___145_4024.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4023 FStar_Syntax_Syntax.U_unknown in
                        let uu____4025 =
                          let uu____4026 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4026 in
                        FStar_Util.Inl uu____4025
                    | FStar_Util.Inr (eff_name,uu____4033) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4064 =
                        let uu____4065 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4065 in
                      FStar_All.pipe_right uu____4064
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4077 =
                        let uu____4078 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4078 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4086 =
                          let uu____4087 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4087 in
                        FStar_All.pipe_right uu____4086
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4091 =
                             let uu____4092 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4092 in
                           FStar_All.pipe_right uu____4091
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4103 =
                         let uu____4104 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4104 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4103);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4119 =
                       (is_impure lc1) &&
                         (let uu____4120 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4120) in
                     if uu____4119
                     then fallback ()
                     else
                       (let uu____4124 = encode_binders None bs1 env in
                        match uu____4124 with
                        | (vars,guards,envbody,decls,uu____4139) ->
                            let uu____4146 =
                              let uu____4154 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4154
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4146 with
                             | (lc2,body2) ->
                                 let uu____4179 = encode_term body2 envbody in
                                 (match uu____4179 with
                                  | (body3,decls') ->
                                      let key_body =
                                        let uu____4187 =
                                          let uu____4193 =
                                            let uu____4194 =
                                              let uu____4197 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____4197, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____4194 in
                                          ([], vars, uu____4193) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4187 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____4208 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____4208 with
                                       | Some (t1,uu____4223,uu____4224) ->
                                           let uu____4234 =
                                             let uu____4235 =
                                               let uu____4239 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (t1, uu____4239) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4235 in
                                           (uu____4234, [])
                                       | None  ->
                                           let uu____4250 =
                                             is_eta env vars body3 in
                                           (match uu____4250 with
                                            | Some t1 -> (t1, [])
                                            | None  ->
                                                let cvar_sorts =
                                                  FStar_List.map Prims.snd
                                                    cvars in
                                                let fsym =
                                                  let module_name =
                                                    let uu____4262 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env.tcenv in
                                                    FStar_All.pipe_right
                                                      uu____4262
                                                      FStar_Ident.string_of_lid in
                                                  let fsym =
                                                    let uu____4264 =
                                                      let uu____4265 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____4265 in
                                                    varops.mk_unique
                                                      uu____4264 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      None) in
                                                let f =
                                                  let uu____4270 =
                                                    let uu____4274 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars in
                                                    (fsym, uu____4274) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4270 in
                                                let app = mk_Apply f vars in
                                                let typing_f =
                                                  let uu____4282 =
                                                    codomain_eff lc2 in
                                                  match uu____4282 with
                                                  | None  -> []
                                                  | Some c ->
                                                      let tfun =
                                                        FStar_Syntax_Util.arrow
                                                          bs1 c in
                                                      let uu____4289 =
                                                        encode_term_pred None
                                                          tfun env f in
                                                      (match uu____4289 with
                                                       | (f_has_t,decls'') ->
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym in
                                                           let uu____4296 =
                                                             let uu____4298 =
                                                               let uu____4299
                                                                 =
                                                                 let uu____4303
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkForall
                                                                    ([[f]],
                                                                    cvars,
                                                                    f_has_t) in
                                                                 (uu____4303,
                                                                   (Some
                                                                    a_name),
                                                                   a_name) in
                                                               FStar_SMTEncoding_Term.Assume
                                                                 uu____4299 in
                                                             [uu____4298] in
                                                           FStar_List.append
                                                             decls''
                                                             uu____4296) in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____4311 =
                                                    let uu____4315 =
                                                      let uu____4316 =
                                                        let uu____4322 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars),
                                                          uu____4322) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____4316 in
                                                    (uu____4315,
                                                      (Some a_name), a_name) in
                                                  FStar_SMTEncoding_Term.Assume
                                                    uu____4311 in
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
           ((uu____4340,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4341;
                          FStar_Syntax_Syntax.lbunivs = uu____4342;
                          FStar_Syntax_Syntax.lbtyp = uu____4343;
                          FStar_Syntax_Syntax.lbeff = uu____4344;
                          FStar_Syntax_Syntax.lbdef = uu____4345;_}::uu____4346),uu____4347)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4365;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4367;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4383 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4396 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4396, [decl_e])))
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
              let uu____4438 = encode_term e1 env in
              match uu____4438 with
              | (ee1,decls1) ->
                  let uu____4445 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4445 with
                   | (xs,e21) ->
                       let uu____4459 = FStar_List.hd xs in
                       (match uu____4459 with
                        | (x1,uu____4467) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4469 = encode_body e21 env' in
                            (match uu____4469 with
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
            let uu____4491 =
              let uu____4495 =
                let uu____4496 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4496 in
              gen_term_var env uu____4495 in
            match uu____4491 with
            | (scrsym,scr',env1) ->
                let uu____4510 = encode_term e env1 in
                (match uu____4510 with
                 | (scr,decls) ->
                     let uu____4517 =
                       let encode_branch b uu____4533 =
                         match uu____4533 with
                         | (else_case,decls1) ->
                             let uu____4544 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4544 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4574  ->
                                       fun uu____4575  ->
                                         match (uu____4574, uu____4575) with
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
                                                       fun uu____4612  ->
                                                         match uu____4612
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4617 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4632 =
                                                     encode_term w1 env2 in
                                                   (match uu____4632 with
                                                    | (w2,decls21) ->
                                                        let uu____4640 =
                                                          let uu____4641 =
                                                            let uu____4644 =
                                                              let uu____4645
                                                                =
                                                                let uu____4648
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4648) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4645 in
                                                            (guard,
                                                              uu____4644) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4641 in
                                                        (uu____4640, decls21)) in
                                             (match uu____4617 with
                                              | (guard1,decls21) ->
                                                  let uu____4656 =
                                                    encode_br br env2 in
                                                  (match uu____4656 with
                                                   | (br1,decls3) ->
                                                       let uu____4664 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4664,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4517 with
                      | (match_tm,decls1) ->
                          let uu____4676 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4676, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4707 -> let uu____4708 = encode_one_pat env pat in [uu____4708]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4720 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4720
       then
         let uu____4721 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4721
       else ());
      (let uu____4723 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4723 with
       | (vars,pat_term) ->
           let uu____4733 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4756  ->
                     fun v1  ->
                       match uu____4756 with
                       | (env1,vars1) ->
                           let uu____4784 = gen_term_var env1 v1 in
                           (match uu____4784 with
                            | (xx,uu____4796,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4733 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4843 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4851 =
                        let uu____4854 = encode_const c in
                        (scrutinee, uu____4854) in
                      FStar_SMTEncoding_Util.mkEq uu____4851
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4873 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4873 with
                        | (uu____4877,uu____4878::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4880 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4901  ->
                                  match uu____4901 with
                                  | (arg,uu____4907) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4917 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4917)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4936 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4951 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4966 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4988  ->
                                  match uu____4988 with
                                  | (arg,uu____4997) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5007 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5007)) in
                      FStar_All.pipe_right uu____4966 FStar_List.flatten in
                let pat_term1 uu____5023 = encode_term pat_term env1 in
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
      let uu____5030 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5045  ->
                fun uu____5046  ->
                  match (uu____5045, uu____5046) with
                  | ((tms,decls),(t,uu____5066)) ->
                      let uu____5077 = encode_term t env in
                      (match uu____5077 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5030 with | (l1,decls) -> ((FStar_List.rev l1), decls)
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
            let uu____5115 = FStar_Syntax_Util.list_elements e in
            match uu____5115 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 []) in
          let one_pat p =
            let uu____5133 =
              let uu____5143 = FStar_Syntax_Util.unmeta p in
              FStar_All.pipe_right uu____5143 FStar_Syntax_Util.head_and_args in
            match uu____5133 with
            | (head1,args) ->
                let uu____5174 =
                  let uu____5182 =
                    let uu____5183 = FStar_Syntax_Util.un_uinst head1 in
                    uu____5183.FStar_Syntax_Syntax.n in
                  (uu____5182, args) in
                (match uu____5174 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5197,uu____5198)::(e,uu____5200)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5231)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5252 -> failwith "Unexpected pattern term") in
          let lemma_pats p =
            let elts = list_elements1 p in
            let smt_pat_or t1 =
              let uu____5285 =
                let uu____5295 = FStar_Syntax_Util.unmeta t1 in
                FStar_All.pipe_right uu____5295
                  FStar_Syntax_Util.head_and_args in
              match uu____5285 with
              | (head1,args) ->
                  let uu____5324 =
                    let uu____5332 =
                      let uu____5333 = FStar_Syntax_Util.un_uinst head1 in
                      uu____5333.FStar_Syntax_Syntax.n in
                    (uu____5332, args) in
                  (match uu____5324 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5346)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5366 -> None) in
            match elts with
            | t1::[] ->
                let uu____5384 = smt_pat_or t1 in
                (match uu____5384 with
                 | Some e ->
                     let uu____5400 = list_elements1 e in
                     FStar_All.pipe_right uu____5400
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5417 = list_elements1 branch1 in
                             FStar_All.pipe_right uu____5417
                               (FStar_List.map one_pat)))
                 | uu____5431 ->
                     let uu____5435 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat) in
                     [uu____5435])
            | uu____5466 ->
                let uu____5468 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat) in
                [uu____5468] in
          let uu____5499 =
            let uu____5515 =
              let uu____5516 = FStar_Syntax_Subst.compress t in
              uu____5516.FStar_Syntax_Syntax.n in
            match uu____5515 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5546 = FStar_Syntax_Subst.open_comp binders c in
                (match uu____5546 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5581;
                            FStar_Syntax_Syntax.effect_name = uu____5582;
                            FStar_Syntax_Syntax.result_typ = uu____5583;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5585)::(post,uu____5587)::(pats,uu____5589)::[];
                            FStar_Syntax_Syntax.flags = uu____5590;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats in
                          let uu____5624 = lemma_pats pats' in
                          (binders1, pre, post, uu____5624)
                      | uu____5643 -> failwith "impos"))
            | uu____5659 -> failwith "Impos" in
          match uu____5499 with
          | (binders,pre,post,patterns) ->
              let uu____5703 = encode_binders None binders env in
              (match uu____5703 with
               | (vars,guards,env1,decls,uu____5718) ->
                   let uu____5725 =
                     let uu____5732 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5763 =
                                 let uu____5768 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5784  ->
                                           match uu____5784 with
                                           | (t1,uu____5791) ->
                                               encode_term t1
                                                 (let uu___146_5794 = env1 in
                                                  {
                                                    bindings =
                                                      (uu___146_5794.bindings);
                                                    depth =
                                                      (uu___146_5794.depth);
                                                    tcenv =
                                                      (uu___146_5794.tcenv);
                                                    warn =
                                                      (uu___146_5794.warn);
                                                    cache =
                                                      (uu___146_5794.cache);
                                                    nolabels =
                                                      (uu___146_5794.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___146_5794.encode_non_total_function_typ)
                                                  }))) in
                                 FStar_All.pipe_right uu____5768
                                   FStar_List.unzip in
                               match uu____5763 with
                               | (pats,decls1) -> (pats, decls1))) in
                     FStar_All.pipe_right uu____5732 FStar_List.unzip in
                   (match uu____5725 with
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
                                           let uu____5858 =
                                             let uu____5859 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5859 e in
                                           uu____5858 :: p))
                               | uu____5860 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5889 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e in
                                                 uu____5889 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5897 =
                                           let uu____5898 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort) in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5898 tl1 in
                                         aux uu____5897 vars2
                                     | uu____5899 -> pats in
                                   let uu____5903 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort) in
                                   aux uu____5903 vars) in
                        let env2 =
                          let uu___147_5905 = env1 in
                          {
                            bindings = (uu___147_5905.bindings);
                            depth = (uu___147_5905.depth);
                            tcenv = (uu___147_5905.tcenv);
                            warn = (uu___147_5905.warn);
                            cache = (uu___147_5905.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___147_5905.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___147_5905.encode_non_total_function_typ)
                          } in
                        let uu____5906 =
                          let uu____5909 = FStar_Syntax_Util.unmeta pre in
                          encode_formula uu____5909 env2 in
                        (match uu____5906 with
                         | (pre1,decls'') ->
                             let uu____5914 =
                               let uu____5917 = FStar_Syntax_Util.unmeta post in
                               encode_formula uu____5917 env2 in
                             (match uu____5914 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls''')) in
                                  let uu____5924 =
                                    let uu____5925 =
                                      let uu____5931 =
                                        let uu____5932 =
                                          let uu____5935 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards) in
                                          (uu____5935, post1) in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5932 in
                                      (pats1, vars, uu____5931) in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5925 in
                                  (uu____5924, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5948 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5948
        then
          let uu____5949 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5950 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5949 uu____5950
        else () in
      let enc f r l =
        let uu____5977 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5990 = encode_term (Prims.fst x) env in
                 match uu____5990 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5977 with
        | (decls,args) ->
            let uu____6007 =
              let uu___148_6008 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___148_6008.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___148_6008.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6007, decls) in
      let const_op f r uu____6027 = let uu____6030 = f r in (uu____6030, []) in
      let un_op f l =
        let uu____6046 = FStar_List.hd l in FStar_All.pipe_left f uu____6046 in
      let bin_op f uu___120_6059 =
        match uu___120_6059 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6067 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6094 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6103  ->
                 match uu____6103 with
                 | (t,uu____6111) ->
                     let uu____6112 = encode_formula t env in
                     (match uu____6112 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6094 with
        | (decls,phis) ->
            let uu____6129 =
              let uu___149_6130 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___149_6130.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___149_6130.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6129, decls) in
      let eq_op r uu___121_6146 =
        match uu___121_6146 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6206 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6206 r [e1; e2]
        | l ->
            let uu____6226 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6226 r l in
      let mk_imp1 r uu___122_6245 =
        match uu___122_6245 with
        | (lhs,uu____6249)::(rhs,uu____6251)::[] ->
            let uu____6272 = encode_formula rhs env in
            (match uu____6272 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6281) ->
                      (l1, decls1)
                  | uu____6284 ->
                      let uu____6285 = encode_formula lhs env in
                      (match uu____6285 with
                       | (l2,decls2) ->
                           let uu____6292 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6292, (FStar_List.append decls1 decls2)))))
        | uu____6294 -> failwith "impossible" in
      let mk_ite r uu___123_6309 =
        match uu___123_6309 with
        | (guard,uu____6313)::(_then,uu____6315)::(_else,uu____6317)::[] ->
            let uu____6346 = encode_formula guard env in
            (match uu____6346 with
             | (g,decls1) ->
                 let uu____6353 = encode_formula _then env in
                 (match uu____6353 with
                  | (t,decls2) ->
                      let uu____6360 = encode_formula _else env in
                      (match uu____6360 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6369 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6388 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6388 in
      let connectives =
        let uu____6400 =
          let uu____6409 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6409) in
        let uu____6422 =
          let uu____6432 =
            let uu____6441 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6441) in
          let uu____6454 =
            let uu____6464 =
              let uu____6474 =
                let uu____6483 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6483) in
              let uu____6496 =
                let uu____6506 =
                  let uu____6516 =
                    let uu____6525 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6525) in
                  [uu____6516;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6506 in
              uu____6474 :: uu____6496 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6464 in
          uu____6432 :: uu____6454 in
        uu____6400 :: uu____6422 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6687 = encode_formula phi' env in
            (match uu____6687 with
             | (phi2,decls) ->
                 let uu____6694 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6694, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6695 ->
            let uu____6700 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6700 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6729 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6729 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6737;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6739;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6755 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6755 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6787::(x,uu____6789)::(t,uu____6791)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6825 = encode_term x env in
                 (match uu____6825 with
                  | (x1,decls) ->
                      let uu____6832 = encode_term t env in
                      (match uu____6832 with
                       | (t1,decls') ->
                           let uu____6839 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6839, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6843)::(msg,uu____6845)::(phi2,uu____6847)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6881 =
                   let uu____6884 =
                     let uu____6885 = FStar_Syntax_Subst.compress r in
                     uu____6885.FStar_Syntax_Syntax.n in
                   let uu____6888 =
                     let uu____6889 = FStar_Syntax_Subst.compress msg in
                     uu____6889.FStar_Syntax_Syntax.n in
                   (uu____6884, uu____6888) in
                 (match uu____6881 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6896))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6912 -> fallback phi2)
             | uu____6915 when head_redex env head2 ->
                 let uu____6923 = whnf env phi1 in
                 encode_formula uu____6923 env
             | uu____6924 ->
                 let uu____6932 = encode_term phi1 env in
                 (match uu____6932 with
                  | (tt,decls) ->
                      let uu____6939 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___150_6940 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___150_6940.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___150_6940.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6939, decls)))
        | uu____6943 ->
            let uu____6944 = encode_term phi1 env in
            (match uu____6944 with
             | (tt,decls) ->
                 let uu____6951 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___151_6952 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___151_6952.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___151_6952.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6951, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6979 = encode_binders None bs env1 in
        match uu____6979 with
        | (vars,guards,env2,decls,uu____7001) ->
            let uu____7008 =
              let uu____7015 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7038 =
                          let uu____7043 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7057  ->
                                    match uu____7057 with
                                    | (t,uu____7063) ->
                                        encode_term t
                                          (let uu___152_7064 = env2 in
                                           {
                                             bindings =
                                               (uu___152_7064.bindings);
                                             depth = (uu___152_7064.depth);
                                             tcenv = (uu___152_7064.tcenv);
                                             warn = (uu___152_7064.warn);
                                             cache = (uu___152_7064.cache);
                                             nolabels =
                                               (uu___152_7064.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___152_7064.encode_non_total_function_typ)
                                           }))) in
                          FStar_All.pipe_right uu____7043 FStar_List.unzip in
                        match uu____7038 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7015 FStar_List.unzip in
            (match uu____7008 with
             | (pats,decls') ->
                 let uu____7116 = encode_formula body env2 in
                 (match uu____7116 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7135;
                             FStar_SMTEncoding_Term.rng = uu____7136;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7144 -> guards in
                      let uu____7147 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7147, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7181  ->
                   match uu____7181 with
                   | (x,uu____7185) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7191 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7197 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7197) uu____7191 tl1 in
             let uu____7199 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7211  ->
                       match uu____7211 with
                       | (b,uu____7215) ->
                           let uu____7216 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7216)) in
             (match uu____7199 with
              | None  -> ()
              | Some (x,uu____7220) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7230 =
                    let uu____7231 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7231 in
                  FStar_Errors.warn pos uu____7230) in
       let uu____7232 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7232 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7238 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7274  ->
                     match uu____7274 with
                     | (l,uu____7284) -> FStar_Ident.lid_equals op l)) in
           (match uu____7238 with
            | None  -> fallback phi1
            | Some (uu____7307,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7336 = encode_q_body env vars pats body in
             match uu____7336 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7362 =
                     let uu____7368 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7368) in
                   FStar_SMTEncoding_Term.mkForall uu____7362
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7380 = encode_q_body env vars pats body in
             match uu____7380 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7405 =
                   let uu____7406 =
                     let uu____7412 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7412) in
                   FStar_SMTEncoding_Term.mkExists uu____7406
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7405, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7461 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7461 with
  | (asym,a) ->
      let uu____7466 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7466 with
       | (xsym,x) ->
           let uu____7471 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7471 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7501 =
                      let uu____7507 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7507, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7501 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7522 =
                      let uu____7526 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7526) in
                    FStar_SMTEncoding_Util.mkApp uu____7522 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7534 =
                    let uu____7536 =
                      let uu____7538 =
                        let uu____7540 =
                          let uu____7541 =
                            let uu____7545 =
                              let uu____7546 =
                                let uu____7552 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7552) in
                              FStar_SMTEncoding_Util.mkForall uu____7546 in
                            (uu____7545, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Term.Assume uu____7541 in
                        let uu____7561 =
                          let uu____7563 =
                            let uu____7564 =
                              let uu____7568 =
                                let uu____7569 =
                                  let uu____7575 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7575) in
                                FStar_SMTEncoding_Util.mkForall uu____7569 in
                              (uu____7568,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Term.Assume uu____7564 in
                          [uu____7563] in
                        uu____7540 :: uu____7561 in
                      xtok_decl :: uu____7538 in
                    xname_decl :: uu____7536 in
                  (xtok1, uu____7534) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7624 =
                    let uu____7632 =
                      let uu____7638 =
                        let uu____7639 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7639 in
                      quant axy uu____7638 in
                    (FStar_Syntax_Const.op_Eq, uu____7632) in
                  let uu____7645 =
                    let uu____7654 =
                      let uu____7662 =
                        let uu____7668 =
                          let uu____7669 =
                            let uu____7670 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7670 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7669 in
                        quant axy uu____7668 in
                      (FStar_Syntax_Const.op_notEq, uu____7662) in
                    let uu____7676 =
                      let uu____7685 =
                        let uu____7693 =
                          let uu____7699 =
                            let uu____7700 =
                              let uu____7701 =
                                let uu____7704 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7705 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7704, uu____7705) in
                              FStar_SMTEncoding_Util.mkLT uu____7701 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7700 in
                          quant xy uu____7699 in
                        (FStar_Syntax_Const.op_LT, uu____7693) in
                      let uu____7711 =
                        let uu____7720 =
                          let uu____7728 =
                            let uu____7734 =
                              let uu____7735 =
                                let uu____7736 =
                                  let uu____7739 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7740 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7739, uu____7740) in
                                FStar_SMTEncoding_Util.mkLTE uu____7736 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7735 in
                            quant xy uu____7734 in
                          (FStar_Syntax_Const.op_LTE, uu____7728) in
                        let uu____7746 =
                          let uu____7755 =
                            let uu____7763 =
                              let uu____7769 =
                                let uu____7770 =
                                  let uu____7771 =
                                    let uu____7774 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7775 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7774, uu____7775) in
                                  FStar_SMTEncoding_Util.mkGT uu____7771 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7770 in
                              quant xy uu____7769 in
                            (FStar_Syntax_Const.op_GT, uu____7763) in
                          let uu____7781 =
                            let uu____7790 =
                              let uu____7798 =
                                let uu____7804 =
                                  let uu____7805 =
                                    let uu____7806 =
                                      let uu____7809 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7810 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7809, uu____7810) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7806 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7805 in
                                quant xy uu____7804 in
                              (FStar_Syntax_Const.op_GTE, uu____7798) in
                            let uu____7816 =
                              let uu____7825 =
                                let uu____7833 =
                                  let uu____7839 =
                                    let uu____7840 =
                                      let uu____7841 =
                                        let uu____7844 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7845 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7844, uu____7845) in
                                      FStar_SMTEncoding_Util.mkSub uu____7841 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7840 in
                                  quant xy uu____7839 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7833) in
                              let uu____7851 =
                                let uu____7860 =
                                  let uu____7868 =
                                    let uu____7874 =
                                      let uu____7875 =
                                        let uu____7876 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7876 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7875 in
                                    quant qx uu____7874 in
                                  (FStar_Syntax_Const.op_Minus, uu____7868) in
                                let uu____7882 =
                                  let uu____7891 =
                                    let uu____7899 =
                                      let uu____7905 =
                                        let uu____7906 =
                                          let uu____7907 =
                                            let uu____7910 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7911 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7910, uu____7911) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7907 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7906 in
                                      quant xy uu____7905 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7899) in
                                  let uu____7917 =
                                    let uu____7926 =
                                      let uu____7934 =
                                        let uu____7940 =
                                          let uu____7941 =
                                            let uu____7942 =
                                              let uu____7945 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7946 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7945, uu____7946) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7942 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7941 in
                                        quant xy uu____7940 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7934) in
                                    let uu____7952 =
                                      let uu____7961 =
                                        let uu____7969 =
                                          let uu____7975 =
                                            let uu____7976 =
                                              let uu____7977 =
                                                let uu____7980 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7981 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7980, uu____7981) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7977 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7976 in
                                          quant xy uu____7975 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7969) in
                                      let uu____7987 =
                                        let uu____7996 =
                                          let uu____8004 =
                                            let uu____8010 =
                                              let uu____8011 =
                                                let uu____8012 =
                                                  let uu____8015 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8016 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8015, uu____8016) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8012 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8011 in
                                            quant xy uu____8010 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8004) in
                                        let uu____8022 =
                                          let uu____8031 =
                                            let uu____8039 =
                                              let uu____8045 =
                                                let uu____8046 =
                                                  let uu____8047 =
                                                    let uu____8050 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8051 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8050, uu____8051) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8047 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8046 in
                                              quant xy uu____8045 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8039) in
                                          let uu____8057 =
                                            let uu____8066 =
                                              let uu____8074 =
                                                let uu____8080 =
                                                  let uu____8081 =
                                                    let uu____8082 =
                                                      let uu____8085 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8086 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8085,
                                                        uu____8086) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8082 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8081 in
                                                quant xy uu____8080 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8074) in
                                            let uu____8092 =
                                              let uu____8101 =
                                                let uu____8109 =
                                                  let uu____8115 =
                                                    let uu____8116 =
                                                      let uu____8117 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8117 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8116 in
                                                  quant qx uu____8115 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8109) in
                                              [uu____8101] in
                                            uu____8066 :: uu____8092 in
                                          uu____8031 :: uu____8057 in
                                        uu____7996 :: uu____8022 in
                                      uu____7961 :: uu____7987 in
                                    uu____7926 :: uu____7952 in
                                  uu____7891 :: uu____7917 in
                                uu____7860 :: uu____7882 in
                              uu____7825 :: uu____7851 in
                            uu____7790 :: uu____7816 in
                          uu____7755 :: uu____7781 in
                        uu____7720 :: uu____7746 in
                      uu____7685 :: uu____7711 in
                    uu____7654 :: uu____7676 in
                  uu____7624 :: uu____7645 in
                let mk1 l v1 =
                  let uu____8245 =
                    let uu____8250 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8282  ->
                              match uu____8282 with
                              | (l',uu____8291) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8250
                      (FStar_Option.map
                         (fun uu____8324  ->
                            match uu____8324 with | (uu____8335,b) -> b v1)) in
                  FStar_All.pipe_right uu____8245 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8376  ->
                          match uu____8376 with
                          | (l',uu____8385) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8411 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8411 with
        | (xxsym,xx) ->
            let uu____8416 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8416 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name =
                   let uu____8424 =
                     FStar_TypeChecker_Env.current_module env.tcenv in
                   FStar_All.pipe_right uu____8424 FStar_Ident.string_of_lid in
                 let uu____8425 =
                   let uu____8429 =
                     let uu____8430 =
                       let uu____8436 =
                         let uu____8437 =
                           let uu____8440 =
                             let uu____8441 =
                               let uu____8444 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8444) in
                             FStar_SMTEncoding_Util.mkEq uu____8441 in
                           (xx_has_type, uu____8440) in
                         FStar_SMTEncoding_Util.mkImp uu____8437 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8436) in
                     FStar_SMTEncoding_Util.mkForall uu____8430 in
                   let uu____8457 =
                     let uu____8458 =
                       let uu____8459 =
                         let uu____8460 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8460 in
                       Prims.strcat module_name uu____8459 in
                     varops.mk_unique uu____8458 in
                   (uu____8429, (Some "pretyping"), uu____8457) in
                 FStar_SMTEncoding_Term.Assume uu____8425)
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
    let uu____8490 =
      let uu____8491 =
        let uu____8495 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8495, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Term.Assume uu____8491 in
    let uu____8497 =
      let uu____8499 =
        let uu____8500 =
          let uu____8504 =
            let uu____8505 =
              let uu____8511 =
                let uu____8512 =
                  let uu____8515 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8515) in
                FStar_SMTEncoding_Util.mkImp uu____8512 in
              ([[typing_pred]], [xx], uu____8511) in
            mkForall_fuel uu____8505 in
          (uu____8504, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8500 in
      [uu____8499] in
    uu____8490 :: uu____8497 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8543 =
      let uu____8544 =
        let uu____8548 =
          let uu____8549 =
            let uu____8555 =
              let uu____8558 =
                let uu____8560 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8560] in
              [uu____8558] in
            let uu____8563 =
              let uu____8564 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8564 tt in
            (uu____8555, [bb], uu____8563) in
          FStar_SMTEncoding_Util.mkForall uu____8549 in
        (uu____8548, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Term.Assume uu____8544 in
    let uu____8575 =
      let uu____8577 =
        let uu____8578 =
          let uu____8582 =
            let uu____8583 =
              let uu____8589 =
                let uu____8590 =
                  let uu____8593 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8593) in
                FStar_SMTEncoding_Util.mkImp uu____8590 in
              ([[typing_pred]], [xx], uu____8589) in
            mkForall_fuel uu____8583 in
          (uu____8582, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8578 in
      [uu____8577] in
    uu____8543 :: uu____8575 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8627 =
        let uu____8628 =
          let uu____8632 =
            let uu____8634 =
              let uu____8636 =
                let uu____8638 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8639 =
                  let uu____8641 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8641] in
                uu____8638 :: uu____8639 in
              tt :: uu____8636 in
            tt :: uu____8634 in
          ("Prims.Precedes", uu____8632) in
        FStar_SMTEncoding_Util.mkApp uu____8628 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8627 in
    let precedes_y_x =
      let uu____8644 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8644 in
    let uu____8646 =
      let uu____8647 =
        let uu____8651 =
          let uu____8652 =
            let uu____8658 =
              let uu____8661 =
                let uu____8663 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8663] in
              [uu____8661] in
            let uu____8666 =
              let uu____8667 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8667 tt in
            (uu____8658, [bb], uu____8666) in
          FStar_SMTEncoding_Util.mkForall uu____8652 in
        (uu____8651, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Term.Assume uu____8647 in
    let uu____8678 =
      let uu____8680 =
        let uu____8681 =
          let uu____8685 =
            let uu____8686 =
              let uu____8692 =
                let uu____8693 =
                  let uu____8696 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8696) in
                FStar_SMTEncoding_Util.mkImp uu____8693 in
              ([[typing_pred]], [xx], uu____8692) in
            mkForall_fuel uu____8686 in
          (uu____8685, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8681 in
      let uu____8709 =
        let uu____8711 =
          let uu____8712 =
            let uu____8716 =
              let uu____8717 =
                let uu____8723 =
                  let uu____8724 =
                    let uu____8727 =
                      let uu____8728 =
                        let uu____8730 =
                          let uu____8732 =
                            let uu____8734 =
                              let uu____8735 =
                                let uu____8738 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8739 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8738, uu____8739) in
                              FStar_SMTEncoding_Util.mkGT uu____8735 in
                            let uu____8740 =
                              let uu____8742 =
                                let uu____8743 =
                                  let uu____8746 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8747 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8746, uu____8747) in
                                FStar_SMTEncoding_Util.mkGTE uu____8743 in
                              let uu____8748 =
                                let uu____8750 =
                                  let uu____8751 =
                                    let uu____8754 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8755 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8754, uu____8755) in
                                  FStar_SMTEncoding_Util.mkLT uu____8751 in
                                [uu____8750] in
                              uu____8742 :: uu____8748 in
                            uu____8734 :: uu____8740 in
                          typing_pred_y :: uu____8732 in
                        typing_pred :: uu____8730 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8728 in
                    (uu____8727, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8724 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8723) in
              mkForall_fuel uu____8717 in
            (uu____8716, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Term.Assume uu____8712 in
        [uu____8711] in
      uu____8680 :: uu____8709 in
    uu____8646 :: uu____8678 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8785 =
      let uu____8786 =
        let uu____8790 =
          let uu____8791 =
            let uu____8797 =
              let uu____8800 =
                let uu____8802 = FStar_SMTEncoding_Term.boxString b in
                [uu____8802] in
              [uu____8800] in
            let uu____8805 =
              let uu____8806 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8806 tt in
            (uu____8797, [bb], uu____8805) in
          FStar_SMTEncoding_Util.mkForall uu____8791 in
        (uu____8790, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Term.Assume uu____8786 in
    let uu____8817 =
      let uu____8819 =
        let uu____8820 =
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
          (uu____8824, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8820 in
      [uu____8819] in
    uu____8785 :: uu____8817 in
  let mk_ref1 env reft_name uu____8857 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8868 =
        let uu____8872 =
          let uu____8874 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8874] in
        (reft_name, uu____8872) in
      FStar_SMTEncoding_Util.mkApp uu____8868 in
    let refb =
      let uu____8877 =
        let uu____8881 =
          let uu____8883 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8883] in
        (reft_name, uu____8881) in
      FStar_SMTEncoding_Util.mkApp uu____8877 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8887 =
      let uu____8888 =
        let uu____8892 =
          let uu____8893 =
            let uu____8899 =
              let uu____8900 =
                let uu____8903 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8903) in
              FStar_SMTEncoding_Util.mkImp uu____8900 in
            ([[typing_pred]], [xx; aa], uu____8899) in
          mkForall_fuel uu____8893 in
        (uu____8892, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Term.Assume uu____8888 in
    let uu____8918 =
      let uu____8920 =
        let uu____8921 =
          let uu____8925 =
            let uu____8926 =
              let uu____8932 =
                let uu____8933 =
                  let uu____8936 =
                    FStar_SMTEncoding_Util.mkAnd (typing_pred, typing_pred_b) in
                  let uu____8937 =
                    let uu____8938 =
                      let uu____8941 = FStar_SMTEncoding_Util.mkFreeV aa in
                      let uu____8942 = FStar_SMTEncoding_Util.mkFreeV bb in
                      (uu____8941, uu____8942) in
                    FStar_SMTEncoding_Util.mkEq uu____8938 in
                  (uu____8936, uu____8937) in
                FStar_SMTEncoding_Util.mkImp uu____8933 in
              ([[typing_pred; typing_pred_b]], [xx; aa; bb], uu____8932) in
            mkForall_fuel' (Prims.parse_int "2") uu____8926 in
          (uu____8925, (Some "ref typing is injective"), "ref_injectivity") in
        FStar_SMTEncoding_Term.Assume uu____8921 in
      [uu____8920] in
    uu____8887 :: uu____8918 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8984 =
      let uu____8985 =
        let uu____8989 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8989, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Term.Assume uu____8985 in
    [uu____8984] in
  let mk_and_interp env conj uu____9000 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9010 =
        let uu____9014 =
          let uu____9016 = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
          [uu____9016] in
        ("Valid", uu____9014) in
      FStar_SMTEncoding_Util.mkApp uu____9010 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9023 =
      let uu____9024 =
        let uu____9028 =
          let uu____9029 =
            let uu____9035 =
              let uu____9036 =
                let uu____9039 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9039, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9036 in
            ([[valid]], [aa; bb], uu____9035) in
          FStar_SMTEncoding_Util.mkForall uu____9029 in
        (uu____9028, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Term.Assume uu____9024 in
    [uu____9023] in
  let mk_or_interp env disj uu____9063 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9073 =
        let uu____9077 =
          let uu____9079 = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
          [uu____9079] in
        ("Valid", uu____9077) in
      FStar_SMTEncoding_Util.mkApp uu____9073 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9086 =
      let uu____9087 =
        let uu____9091 =
          let uu____9092 =
            let uu____9098 =
              let uu____9099 =
                let uu____9102 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9102, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9099 in
            ([[valid]], [aa; bb], uu____9098) in
          FStar_SMTEncoding_Util.mkForall uu____9092 in
        (uu____9091, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Term.Assume uu____9087 in
    [uu____9086] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let valid =
      let uu____9140 =
        let uu____9144 =
          let uu____9146 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
          [uu____9146] in
        ("Valid", uu____9144) in
      FStar_SMTEncoding_Util.mkApp uu____9140 in
    let uu____9149 =
      let uu____9150 =
        let uu____9154 =
          let uu____9155 =
            let uu____9161 =
              let uu____9162 =
                let uu____9165 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9165, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9162 in
            ([[valid]], [aa; xx1; yy1], uu____9161) in
          FStar_SMTEncoding_Util.mkForall uu____9155 in
        (uu____9154, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Term.Assume uu____9150 in
    [uu____9149] in
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
      let uu____9209 =
        let uu____9213 =
          let uu____9215 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
          [uu____9215] in
        ("Valid", uu____9213) in
      FStar_SMTEncoding_Util.mkApp uu____9209 in
    let uu____9218 =
      let uu____9219 =
        let uu____9223 =
          let uu____9224 =
            let uu____9230 =
              let uu____9231 =
                let uu____9234 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9234, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9231 in
            ([[valid]], [aa; bb; xx1; yy1], uu____9230) in
          FStar_SMTEncoding_Util.mkForall uu____9224 in
        (uu____9223, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Term.Assume uu____9219 in
    [uu____9218] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9272 =
        let uu____9276 =
          let uu____9278 = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
          [uu____9278] in
        ("Valid", uu____9276) in
      FStar_SMTEncoding_Util.mkApp uu____9272 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9285 =
      let uu____9286 =
        let uu____9290 =
          let uu____9291 =
            let uu____9297 =
              let uu____9298 =
                let uu____9301 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9301, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9298 in
            ([[valid]], [aa; bb], uu____9297) in
          FStar_SMTEncoding_Util.mkForall uu____9291 in
        (uu____9290, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Term.Assume uu____9286 in
    [uu____9285] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9335 =
        let uu____9339 =
          let uu____9341 = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
          [uu____9341] in
        ("Valid", uu____9339) in
      FStar_SMTEncoding_Util.mkApp uu____9335 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9348 =
      let uu____9349 =
        let uu____9353 =
          let uu____9354 =
            let uu____9360 =
              let uu____9361 =
                let uu____9364 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9364, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9361 in
            ([[valid]], [aa; bb], uu____9360) in
          FStar_SMTEncoding_Util.mkForall uu____9354 in
        (uu____9353, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Term.Assume uu____9349 in
    [uu____9348] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let valid =
      let uu____9394 =
        let uu____9398 =
          let uu____9400 = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
          [uu____9400] in
        ("Valid", uu____9398) in
      FStar_SMTEncoding_Util.mkApp uu____9394 in
    let not_valid_a =
      let uu____9404 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9404 in
    let uu____9406 =
      let uu____9407 =
        let uu____9411 =
          let uu____9412 =
            let uu____9418 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[valid]], [aa], uu____9418) in
          FStar_SMTEncoding_Util.mkForall uu____9412 in
        (uu____9411, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Term.Assume uu____9407 in
    [uu____9406] in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let valid =
      let uu____9454 =
        let uu____9458 =
          let uu____9460 = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b]) in
          [uu____9460] in
        ("Valid", uu____9458) in
      FStar_SMTEncoding_Util.mkApp uu____9454 in
    let valid_b_x =
      let uu____9464 =
        let uu____9468 =
          let uu____9470 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9470] in
        ("Valid", uu____9468) in
      FStar_SMTEncoding_Util.mkApp uu____9464 in
    let uu____9472 =
      let uu____9473 =
        let uu____9477 =
          let uu____9478 =
            let uu____9484 =
              let uu____9485 =
                let uu____9488 =
                  let uu____9489 =
                    let uu____9495 =
                      let uu____9498 =
                        let uu____9500 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9500] in
                      [uu____9498] in
                    let uu____9503 =
                      let uu____9504 =
                        let uu____9507 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9507, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9504 in
                    (uu____9495, [xx1], uu____9503) in
                  FStar_SMTEncoding_Util.mkForall uu____9489 in
                (uu____9488, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9485 in
            ([[valid]], [aa; bb], uu____9484) in
          FStar_SMTEncoding_Util.mkForall uu____9478 in
        (uu____9477, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Term.Assume uu____9473 in
    [uu____9472] in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let valid =
      let uu____9554 =
        let uu____9558 =
          let uu____9560 = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b]) in
          [uu____9560] in
        ("Valid", uu____9558) in
      FStar_SMTEncoding_Util.mkApp uu____9554 in
    let valid_b_x =
      let uu____9564 =
        let uu____9568 =
          let uu____9570 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9570] in
        ("Valid", uu____9568) in
      FStar_SMTEncoding_Util.mkApp uu____9564 in
    let uu____9572 =
      let uu____9573 =
        let uu____9577 =
          let uu____9578 =
            let uu____9584 =
              let uu____9585 =
                let uu____9588 =
                  let uu____9589 =
                    let uu____9595 =
                      let uu____9598 =
                        let uu____9600 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9600] in
                      [uu____9598] in
                    let uu____9603 =
                      let uu____9604 =
                        let uu____9607 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9607, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9604 in
                    (uu____9595, [xx1], uu____9603) in
                  FStar_SMTEncoding_Util.mkExists uu____9589 in
                (uu____9588, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9585 in
            ([[valid]], [aa; bb], uu____9584) in
          FStar_SMTEncoding_Util.mkForall uu____9578 in
        (uu____9577, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Term.Assume uu____9573 in
    [uu____9572] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9643 =
      let uu____9644 =
        let uu____9648 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9649 = varops.mk_unique "typing_range_const" in
        (uu____9648, (Some "Range_const typing"), uu____9649) in
      FStar_SMTEncoding_Term.Assume uu____9644 in
    [uu____9643] in
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
          let uu____9911 =
            FStar_Util.find_opt
              (fun uu____9929  ->
                 match uu____9929 with
                 | (l,uu____9939) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9911 with
          | None  -> []
          | Some (uu____9961,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9998 = encode_function_type_as_formula None None t env in
        match uu____9998 with
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
            let uu____10030 =
              (let uu____10031 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10031) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10030
            then
              let uu____10035 = new_term_constant_and_tok_from_lid env lid in
              match uu____10035 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10047 =
                      let uu____10048 = FStar_Syntax_Subst.compress t_norm in
                      uu____10048.FStar_Syntax_Syntax.n in
                    match uu____10047 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10053) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10070  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10073 -> [] in
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
              (let uu____10082 = prims.is lid in
               if uu____10082
               then
                 let vname = varops.new_fvar lid in
                 let uu____10087 = prims.mk lid vname in
                 match uu____10087 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10102 =
                    let uu____10108 = curried_arrow_formals_comp t_norm in
                    match uu____10108 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10119 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10119
                          then
                            let uu____10120 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___153_10121 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___153_10121.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___153_10121.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___153_10121.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___153_10121.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___153_10121.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___153_10121.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___153_10121.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___153_10121.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___153_10121.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___153_10121.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___153_10121.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___153_10121.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___153_10121.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___153_10121.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___153_10121.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___153_10121.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___153_10121.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___153_10121.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___153_10121.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___153_10121.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___153_10121.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___153_10121.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___153_10121.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10120
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10128 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10128)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10102 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10155 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10155 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10168 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___124_10192  ->
                                     match uu___124_10192 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10195 =
                                           FStar_Util.prefix vars in
                                         (match uu____10195 with
                                          | (uu____10206,(xxsym,uu____10208))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10218 =
                                                let uu____10219 =
                                                  let uu____10223 =
                                                    let uu____10224 =
                                                      let uu____10230 =
                                                        let uu____10231 =
                                                          let uu____10234 =
                                                            let uu____10235 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10235 in
                                                          (vapp, uu____10234) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10231 in
                                                      ([[vapp]], vars,
                                                        uu____10230) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10224 in
                                                  (uu____10223,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10219 in
                                              [uu____10218])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10246 =
                                           FStar_Util.prefix vars in
                                         (match uu____10246 with
                                          | (uu____10257,(xxsym,uu____10259))
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
                                              let uu____10273 =
                                                let uu____10274 =
                                                  let uu____10278 =
                                                    let uu____10279 =
                                                      let uu____10285 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10285) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10279 in
                                                  (uu____10278,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10274 in
                                              [uu____10273])
                                     | uu____10294 -> [])) in
                           let uu____10295 = encode_binders None formals env1 in
                           (match uu____10295 with
                            | (vars,guards,env',decls1,uu____10311) ->
                                let uu____10318 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10323 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10323, decls1)
                                  | Some p ->
                                      let uu____10325 = encode_formula p env' in
                                      (match uu____10325 with
                                       | (g,ds) ->
                                           let uu____10332 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10332,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10318 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10341 =
                                         let uu____10345 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10345) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10341 in
                                     let uu____10350 =
                                       let vname_decl =
                                         let uu____10355 =
                                           let uu____10361 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10366  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10361,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10355 in
                                       let uu____10371 =
                                         let env2 =
                                           let uu___154_10375 = env1 in
                                           {
                                             bindings =
                                               (uu___154_10375.bindings);
                                             depth = (uu___154_10375.depth);
                                             tcenv = (uu___154_10375.tcenv);
                                             warn = (uu___154_10375.warn);
                                             cache = (uu___154_10375.cache);
                                             nolabels =
                                               (uu___154_10375.nolabels);
                                             use_zfuel_name =
                                               (uu___154_10375.use_zfuel_name);
                                             encode_non_total_function_typ
                                           } in
                                         let uu____10376 =
                                           let uu____10377 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10377 in
                                         if uu____10376
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10371 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             FStar_SMTEncoding_Term.Assume
                                               (tok_typing,
                                                 (Some
                                                    "function token typing"),
                                                 (Prims.strcat
                                                    "function_token_typing_"
                                                    vname)) in
                                           let uu____10388 =
                                             match formals with
                                             | [] ->
                                                 let uu____10397 =
                                                   let uu____10398 =
                                                     let uu____10400 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10400 in
                                                   push_free_var env1 lid
                                                     vname uu____10398 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10397)
                                             | uu____10403 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10408 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10408 in
                                                 let name_tok_corr =
                                                   let uu____10410 =
                                                     let uu____10414 =
                                                       let uu____10415 =
                                                         let uu____10421 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10421) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10415 in
                                                     (uu____10414,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Term.Assume
                                                     uu____10410 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10388 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10350 with
                                      | (decls2,env2) ->
                                          let uu____10445 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10450 =
                                              encode_term res_t1 env' in
                                            match uu____10450 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10458 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10458,
                                                  decls) in
                                          (match uu____10445 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10466 =
                                                   let uu____10470 =
                                                     let uu____10471 =
                                                       let uu____10477 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10477) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10471 in
                                                   (uu____10470,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____10466 in
                                               let freshness =
                                                 let uu____10486 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10486
                                                 then
                                                   let uu____10489 =
                                                     let uu____10490 =
                                                       let uu____10496 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10502 =
                                                         varops.next_id () in
                                                       (vname, uu____10496,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10502) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10490 in
                                                   let uu____10504 =
                                                     let uu____10506 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10506] in
                                                   uu____10489 :: uu____10504
                                                 else [] in
                                               let g =
                                                 let uu____10510 =
                                                   let uu____10512 =
                                                     let uu____10514 =
                                                       let uu____10516 =
                                                         let uu____10518 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10518 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10516 in
                                                     FStar_List.append decls3
                                                       uu____10514 in
                                                   FStar_List.append decls2
                                                     uu____10512 in
                                                 FStar_List.append decls11
                                                   uu____10510 in
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
          let uu____10540 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10540 with
          | None  ->
              let uu____10563 = encode_free_var env x t t_norm [] in
              (match uu____10563 with
               | (decls,env1) ->
                   let uu____10578 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10578 with
                    | (n1,x',uu____10597) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10609) -> ((n1, x1), [], env)
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
          let uu____10642 = encode_free_var env lid t tt quals in
          match uu____10642 with
          | (decls,env1) ->
              let uu____10653 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10653
              then
                let uu____10657 =
                  let uu____10659 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10659 in
                (uu____10657, env1)
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
             (fun uu____10687  ->
                fun lb  ->
                  match uu____10687 with
                  | (decls,env1) ->
                      let uu____10699 =
                        let uu____10703 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10703
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10699 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10717 = FStar_Syntax_Util.head_and_args t in
    match uu____10717 with
    | (hd1,args) ->
        let uu____10743 =
          let uu____10744 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10744.FStar_Syntax_Syntax.n in
        (match uu____10743 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10748,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10761 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10776  ->
      fun quals  ->
        match uu____10776 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10825 = FStar_Util.first_N nbinders formals in
              match uu____10825 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10865  ->
                         fun uu____10866  ->
                           match (uu____10865, uu____10866) with
                           | ((formal,uu____10876),(binder,uu____10878)) ->
                               let uu____10883 =
                                 let uu____10888 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10888) in
                               FStar_Syntax_Syntax.NT uu____10883) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10893 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10907  ->
                              match uu____10907 with
                              | (x,i) ->
                                  let uu____10914 =
                                    let uu___155_10915 = x in
                                    let uu____10916 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___155_10915.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___155_10915.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10916
                                    } in
                                  (uu____10914, i))) in
                    FStar_All.pipe_right uu____10893
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10928 =
                      let uu____10930 =
                        let uu____10931 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10931.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10930 in
                    let uu____10935 =
                      let uu____10936 = FStar_Syntax_Subst.compress body in
                      let uu____10937 =
                        let uu____10938 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10938 in
                      FStar_Syntax_Syntax.extend_app_n uu____10936
                        uu____10937 in
                    uu____10935 uu____10928 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10980 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10980
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___156_10981 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___156_10981.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___156_10981.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___156_10981.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___156_10981.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___156_10981.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___156_10981.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___156_10981.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___156_10981.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___156_10981.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___156_10981.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___156_10981.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___156_10981.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___156_10981.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___156_10981.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___156_10981.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___156_10981.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___156_10981.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___156_10981.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___156_10981.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___156_10981.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___156_10981.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___156_10981.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___156_10981.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11002 = FStar_Syntax_Util.abs_formals e in
                match uu____11002 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11051::uu____11052 ->
                         let uu____11060 =
                           let uu____11061 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11061.FStar_Syntax_Syntax.n in
                         (match uu____11060 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11088 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11088 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11114 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11114
                                   then
                                     let uu____11132 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11132 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11178  ->
                                                   fun uu____11179  ->
                                                     match (uu____11178,
                                                             uu____11179)
                                                     with
                                                     | ((x,uu____11189),
                                                        (b,uu____11191)) ->
                                                         let uu____11196 =
                                                           let uu____11201 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11201) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11196)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11203 =
                                            let uu____11214 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11214) in
                                          (uu____11203, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11249 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11249 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11301) ->
                              let uu____11306 =
                                let uu____11317 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11317 in
                              (uu____11306, true)
                          | uu____11350 when Prims.op_Negation norm1 ->
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
                          | uu____11352 ->
                              let uu____11353 =
                                let uu____11354 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11355 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11354
                                  uu____11355 in
                              failwith uu____11353)
                     | uu____11368 ->
                         let uu____11369 =
                           let uu____11370 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11370.FStar_Syntax_Syntax.n in
                         (match uu____11369 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11397 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11397 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11415 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11415 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11463 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11491 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11491
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11498 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11539  ->
                            fun lb  ->
                              match uu____11539 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11590 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11590
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11593 =
                                      let uu____11601 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11601
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11593 with
                                    | (tok,decl,env2) ->
                                        let uu____11626 =
                                          let uu____11633 =
                                            let uu____11639 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11639, tok) in
                                          uu____11633 :: toks in
                                        (uu____11626, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11498 with
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
                        | uu____11741 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11746 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11746 vars)
                            else
                              (let uu____11748 =
                                 let uu____11752 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11752) in
                               FStar_SMTEncoding_Util.mkApp uu____11748) in
                      let uu____11757 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___125_11759  ->
                                 match uu___125_11759 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11760 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11763 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11763))) in
                      if uu____11757
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11783;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11785;
                                FStar_Syntax_Syntax.lbeff = uu____11786;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11827 =
                                 FStar_Syntax_Subst.univ_var_opening uvs in
                               (match uu____11827 with
                                | (univ_subst,univ_vars1) ->
                                    let env' =
                                      let uu___159_11842 = env1 in
                                      let uu____11843 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1.tcenv univ_vars1 in
                                      {
                                        bindings = (uu___159_11842.bindings);
                                        depth = (uu___159_11842.depth);
                                        tcenv = uu____11843;
                                        warn = (uu___159_11842.warn);
                                        cache = (uu___159_11842.cache);
                                        nolabels = (uu___159_11842.nolabels);
                                        use_zfuel_name =
                                          (uu___159_11842.use_zfuel_name);
                                        encode_non_total_function_typ =
                                          (uu___159_11842.encode_non_total_function_typ)
                                      } in
                                    let t_norm1 =
                                      FStar_Syntax_Subst.subst univ_subst
                                        t_norm in
                                    let e1 =
                                      let uu____11846 =
                                        FStar_Syntax_Subst.subst univ_subst e in
                                      FStar_Syntax_Subst.compress uu____11846 in
                                    let uu____11847 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11847 with
                                     | ((binders,body,uu____11859,uu____11860),curry)
                                         ->
                                         ((let uu____11867 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11867
                                           then
                                             let uu____11868 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11869 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11868 uu____11869
                                           else ());
                                          (let uu____11871 =
                                             encode_binders None binders env' in
                                           match uu____11871 with
                                           | (vars,guards,env'1,binder_decls,uu____11887)
                                               ->
                                               let body1 =
                                                 let uu____11895 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11895
                                                 then
                                                   reify_body env'1.tcenv
                                                     body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11898 =
                                                 let uu____11903 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11903
                                                 then
                                                   let uu____11909 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11910 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11909, uu____11910)
                                                 else
                                                   (let uu____11916 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11916)) in
                                               (match uu____11898 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11930 =
                                                        let uu____11934 =
                                                          let uu____11935 =
                                                            let uu____11941 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11941) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11935 in
                                                        let uu____11947 =
                                                          let uu____11949 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11949 in
                                                        (uu____11934,
                                                          uu____11947,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Term.Assume
                                                        uu____11930 in
                                                    let uu____11951 =
                                                      let uu____11953 =
                                                        let uu____11955 =
                                                          let uu____11957 =
                                                            let uu____11959 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11959 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11957 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11955 in
                                                      FStar_List.append
                                                        decls1 uu____11953 in
                                                    (uu____11951, env1))))))
                           | uu____11962 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11981 = varops.fresh "fuel" in
                             (uu____11981, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____11984 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12023  ->
                                     fun uu____12024  ->
                                       match (uu____12023, uu____12024) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12106 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12106 in
                                           let gtok =
                                             let uu____12108 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12108 in
                                           let env3 =
                                             let uu____12110 =
                                               let uu____12112 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12112 in
                                             push_free_var env2 flid gtok
                                               uu____12110 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____11984 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12196
                                 t_norm uu____12198 =
                                 match (uu____12196, uu____12198) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12223;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12224;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12241 =
                                       FStar_Syntax_Subst.univ_var_opening
                                         uvs in
                                     (match uu____12241 with
                                      | (univ_subst,univ_vars1) ->
                                          let env' =
                                            let uu___160_12258 = env2 in
                                            let uu____12259 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env2.tcenv univ_vars1 in
                                            {
                                              bindings =
                                                (uu___160_12258.bindings);
                                              depth = (uu___160_12258.depth);
                                              tcenv = uu____12259;
                                              warn = (uu___160_12258.warn);
                                              cache = (uu___160_12258.cache);
                                              nolabels =
                                                (uu___160_12258.nolabels);
                                              use_zfuel_name =
                                                (uu___160_12258.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___160_12258.encode_non_total_function_typ)
                                            } in
                                          let t_norm1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst t_norm in
                                          let e1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst e in
                                          ((let uu____12263 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12263
                                            then
                                              let uu____12264 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12265 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12266 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12264 uu____12265
                                                uu____12266
                                            else ());
                                           (let uu____12268 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12268 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12290 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12290
                                                  then
                                                    let uu____12291 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12292 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12293 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12294 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12291 uu____12292
                                                      uu____12293 uu____12294
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12298 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12298 with
                                                  | (vars,guards,env'1,binder_decls,uu____12316)
                                                      ->
                                                      let decl_g =
                                                        let uu____12324 =
                                                          let uu____12330 =
                                                            let uu____12332 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12332 in
                                                          (g, uu____12330,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12324 in
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
                                                        let uu____12347 =
                                                          let uu____12351 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12351) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12347 in
                                                      let gsapp =
                                                        let uu____12357 =
                                                          let uu____12361 =
                                                            let uu____12363 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12363 ::
                                                              vars_tm in
                                                          (g, uu____12361) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12357 in
                                                      let gmax =
                                                        let uu____12367 =
                                                          let uu____12371 =
                                                            let uu____12373 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12373 ::
                                                              vars_tm in
                                                          (g, uu____12371) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12367 in
                                                      let body1 =
                                                        let uu____12377 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12377
                                                        then
                                                          reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12379 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12379 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12390
                                                               =
                                                               let uu____12394
                                                                 =
                                                                 let uu____12395
                                                                   =
                                                                   let uu____12403
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
                                                                    uu____12403) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12395 in
                                                               let uu____12414
                                                                 =
                                                                 let uu____12416
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12416 in
                                                               (uu____12394,
                                                                 uu____12414,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12390 in
                                                           let eqn_f =
                                                             let uu____12419
                                                               =
                                                               let uu____12423
                                                                 =
                                                                 let uu____12424
                                                                   =
                                                                   let uu____12430
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12430) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12424 in
                                                               (uu____12423,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12419 in
                                                           let eqn_g' =
                                                             let uu____12438
                                                               =
                                                               let uu____12442
                                                                 =
                                                                 let uu____12443
                                                                   =
                                                                   let uu____12449
                                                                    =
                                                                    let uu____12450
                                                                    =
                                                                    let uu____12453
                                                                    =
                                                                    let uu____12454
                                                                    =
                                                                    let uu____12458
                                                                    =
                                                                    let uu____12460
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12460
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12458) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12454 in
                                                                    (gsapp,
                                                                    uu____12453) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12450 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12449) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12443 in
                                                               (uu____12442,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12438 in
                                                           let uu____12472 =
                                                             let uu____12477
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12477
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12494)
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
                                                                    let uu____12509
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12509
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12512
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
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Term.Assume
                                                                    uu____12512 in
                                                                 let uu____12534
                                                                   =
                                                                   let uu____12538
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12538
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12546
                                                                    =
                                                                    let uu____12548
                                                                    =
                                                                    let uu____12549
                                                                    =
                                                                    let uu____12553
                                                                    =
                                                                    let uu____12554
                                                                    =
                                                                    let uu____12560
                                                                    =
                                                                    let uu____12561
                                                                    =
                                                                    let uu____12564
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12564,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12561 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12560) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12554 in
                                                                    (uu____12553,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12549 in
                                                                    [uu____12548] in
                                                                    (d3,
                                                                    uu____12546) in
                                                                 (match uu____12534
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12472
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
                               let uu____12599 =
                                 let uu____12606 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12638  ->
                                      fun uu____12639  ->
                                        match (uu____12638, uu____12639) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12715 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12715 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12606 in
                               (match uu____12599 with
                                | (decls2,eqns,env01) ->
                                    let uu____12755 =
                                      let isDeclFun uu___126_12763 =
                                        match uu___126_12763 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12764 -> true
                                        | uu____12770 -> false in
                                      let uu____12771 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12771
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12755 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12798 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12798
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
      (let uu____12831 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____12831
       then
         let uu____12832 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
           uu____12832
       else ());
      (let nm =
         let uu____12835 = FStar_Syntax_Util.lid_of_sigelt se in
         match uu____12835 with | None  -> "" | Some l -> l.FStar_Ident.str in
       let uu____12838 = encode_sigelt' env se in
       match uu____12838 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12847 =
                  let uu____12849 =
                    let uu____12850 = FStar_Util.format1 "<Skipped %s/>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12850 in
                  [uu____12849] in
                (uu____12847, e)
            | uu____12852 ->
                let uu____12853 =
                  let uu____12855 =
                    let uu____12857 =
                      let uu____12858 =
                        FStar_Util.format1 "<Start encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12858 in
                    uu____12857 :: g in
                  let uu____12859 =
                    let uu____12861 =
                      let uu____12862 =
                        FStar_Util.format1 "</end encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12862 in
                    [uu____12861] in
                  FStar_List.append uu____12855 uu____12859 in
                (uu____12853, e)))
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12870 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12879 =
            let uu____12880 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12880 Prims.op_Negation in
          if uu____12879
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12900 ->
                   let uu____12901 =
                     let uu____12904 =
                       let uu____12905 =
                         let uu____12920 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12920) in
                       FStar_Syntax_Syntax.Tm_abs uu____12905 in
                     FStar_Syntax_Syntax.mk uu____12904 in
                   uu____12901 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____12973 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____12973 with
               | (aname,atok,env2) ->
                   let uu____12983 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____12983 with
                    | (formals,uu____12993) ->
                        let uu____13000 =
                          let uu____13003 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13003 env2 in
                        (match uu____13000 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13011 =
                                 let uu____13012 =
                                   let uu____13018 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13026  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13018,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13012 in
                               [uu____13011;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13033 =
                               let aux uu____13062 uu____13063 =
                                 match (uu____13062, uu____13063) with
                                 | ((bv,uu____13090),(env3,acc_sorts,acc)) ->
                                     let uu____13111 = gen_term_var env3 bv in
                                     (match uu____13111 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13033 with
                              | (uu____13149,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13163 =
                                      let uu____13167 =
                                        let uu____13168 =
                                          let uu____13174 =
                                            let uu____13175 =
                                              let uu____13178 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13178) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13175 in
                                          ([[app]], xs_sorts, uu____13174) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13168 in
                                      (uu____13167, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Term.Assume uu____13163 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13190 =
                                      let uu____13194 =
                                        let uu____13195 =
                                          let uu____13201 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13201) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13195 in
                                      (uu____13194,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Term.Assume uu____13190 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13211 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13211 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____13227,uu____13228,uu____13229) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13232 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13232 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13243,t,quals) ->
          let will_encode_definition =
            let uu____13249 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___127_13251  ->
                      match uu___127_13251 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13254 -> false)) in
            Prims.op_Negation uu____13249 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13260 = encode_top_level_val env fv t quals in
             match uu____13260 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13272 =
                   let uu____13274 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13274 in
                 (uu____13272, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____13279) ->
          let uu____13282 = encode_formula f env in
          (match uu____13282 with
           | (f1,decls) ->
               let g =
                 let uu____13291 =
                   let uu____13292 =
                     let uu____13296 =
                       let uu____13298 =
                         let uu____13299 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13299 in
                       Some uu____13298 in
                     let uu____13300 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13296, uu____13300) in
                   FStar_SMTEncoding_Term.Assume uu____13292 in
                 [uu____13291] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13304,quals,uu____13306) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13314 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13321 =
                       let uu____13326 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13326.FStar_Syntax_Syntax.fv_name in
                     uu____13321.FStar_Syntax_Syntax.v in
                   let uu____13330 =
                     let uu____13331 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13331 in
                   if uu____13330
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
                     let uu____13350 = encode_sigelt' env1 val_decl in
                     match uu____13350 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13314 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13367,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13369;
                          FStar_Syntax_Syntax.lbtyp = uu____13370;
                          FStar_Syntax_Syntax.lbeff = uu____13371;
                          FStar_Syntax_Syntax.lbdef = uu____13372;_}::[]),uu____13373,uu____13374,uu____13375)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13391 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13391 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let valid_b2t_x =
                 let uu____13409 =
                   let uu____13413 =
                     let uu____13415 =
                       FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
                     [uu____13415] in
                   ("Valid", uu____13413) in
                 FStar_SMTEncoding_Util.mkApp uu____13409 in
               let decls =
                 let uu____13420 =
                   let uu____13422 =
                     let uu____13423 =
                       let uu____13427 =
                         let uu____13428 =
                           let uu____13434 =
                             let uu____13435 =
                               let uu____13438 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13438) in
                             FStar_SMTEncoding_Util.mkEq uu____13435 in
                           ([[valid_b2t_x]], [xx], uu____13434) in
                         FStar_SMTEncoding_Util.mkForall uu____13428 in
                       (uu____13427, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Term.Assume uu____13423 in
                   [uu____13422] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13420 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let
          (uu____13455,uu____13456,quals,uu____13458) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___128_13466  ->
                  match uu___128_13466 with
                  | FStar_Syntax_Syntax.Discriminator uu____13467 -> true
                  | uu____13468 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13470,lids,quals,uu____13473) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13482 =
                     let uu____13483 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13483.FStar_Ident.idText in
                   uu____13482 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___129_13485  ->
                     match uu___129_13485 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13486 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13489,quals,uu____13491) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___130_13503  ->
                  match uu___130_13503 with
                  | FStar_Syntax_Syntax.Projector uu____13504 -> true
                  | uu____13507 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13514 = try_lookup_free_var env l in
          (match uu____13514 with
           | Some uu____13518 -> ([], env)
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
          ((is_rec,bindings),uu____13527,quals,uu____13529) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13543,uu____13544) ->
          let uu____13551 = encode_signature env ses in
          (match uu____13551 with
           | (g,env1) ->
               let uu____13561 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___131_13571  ->
                         match uu___131_13571 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13572,Some "inversion axiom",uu____13573)
                             -> false
                         | uu____13575 -> true)) in
               (match uu____13561 with
                | (g',inversions) ->
                    let uu____13584 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___132_13594  ->
                              match uu___132_13594 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13595 ->
                                  true
                              | uu____13601 -> false)) in
                    (match uu____13584 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13612,tps,k,uu____13615,datas,quals) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___133_13626  ->
                    match uu___133_13626 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13627 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13634 = c in
              match uu____13634 with
              | (name,args,uu____13638,uu____13639,uu____13640) ->
                  let uu____13643 =
                    let uu____13644 =
                      let uu____13650 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13657  ->
                                match uu____13657 with
                                | (uu____13661,sort,uu____13663) -> sort)) in
                      (name, uu____13650, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13644 in
                  [uu____13643]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13681 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13684 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13684 FStar_Option.isNone)) in
            if uu____13681
            then []
            else
              (let uu____13701 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13701 with
               | (xxsym,xx) ->
                   let uu____13707 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13718  ->
                             fun l  ->
                               match uu____13718 with
                               | (out,decls) ->
                                   let uu____13730 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13730 with
                                    | (uu____13736,data_t) ->
                                        let uu____13738 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13738 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13767 =
                                                 let uu____13768 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13768.FStar_Syntax_Syntax.n in
                                               match uu____13767 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13776,indices) ->
                                                   indices
                                               | uu____13792 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13804  ->
                                                         match uu____13804
                                                         with
                                                         | (x,uu____13808) ->
                                                             let uu____13809
                                                               =
                                                               let uu____13810
                                                                 =
                                                                 let uu____13814
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13814,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13810 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13809)
                                                    env) in
                                             let uu____13816 =
                                               encode_args indices env1 in
                                             (match uu____13816 with
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
                                                      let uu____13836 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13844
                                                                 =
                                                                 let uu____13847
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13847,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13844)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13836
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13849 =
                                                      let uu____13850 =
                                                        let uu____13853 =
                                                          let uu____13854 =
                                                            let uu____13857 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13857,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13854 in
                                                        (out, uu____13853) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13850 in
                                                    (uu____13849,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13707 with
                    | (data_ax,decls) ->
                        let uu____13865 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13865 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13876 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13876 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13879 =
                                 let uu____13883 =
                                   let uu____13884 =
                                     let uu____13890 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13898 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13890,
                                       uu____13898) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13884 in
                                 let uu____13906 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13883, (Some "inversion axiom"),
                                   uu____13906) in
                               FStar_SMTEncoding_Term.Assume uu____13879 in
                             let pattern_guarded_inversion =
                               let uu____13910 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13910
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13918 =
                                   let uu____13919 =
                                     let uu____13923 =
                                       let uu____13924 =
                                         let uu____13930 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13938 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13930, uu____13938) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13924 in
                                     let uu____13946 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13923, (Some "inversion axiom"),
                                       uu____13946) in
                                   FStar_SMTEncoding_Term.Assume uu____13919 in
                                 [uu____13918]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13949 =
            let uu____13957 =
              let uu____13958 = FStar_Syntax_Subst.compress k in
              uu____13958.FStar_Syntax_Syntax.n in
            match uu____13957 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13987 -> (tps, k) in
          (match uu____13949 with
           | (formals,res) ->
               let uu____14002 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14002 with
                | (formals1,res1) ->
                    let uu____14009 = encode_binders None formals1 env in
                    (match uu____14009 with
                     | (vars,guards,env',binder_decls,uu____14024) ->
                         let uu____14031 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14031 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14044 =
                                  let uu____14048 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14048) in
                                FStar_SMTEncoding_Util.mkApp uu____14044 in
                              let uu____14053 =
                                let tname_decl =
                                  let uu____14059 =
                                    let uu____14060 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14075  ->
                                              match uu____14075 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14083 = varops.next_id () in
                                    (tname, uu____14060,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14083, false) in
                                  constructor_or_logic_type_decl uu____14059 in
                                let uu____14088 =
                                  match vars with
                                  | [] ->
                                      let uu____14095 =
                                        let uu____14096 =
                                          let uu____14098 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14098 in
                                        push_free_var env1 t tname
                                          uu____14096 in
                                      ([], uu____14095)
                                  | uu____14102 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14108 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14108 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14117 =
                                          let uu____14121 =
                                            let uu____14122 =
                                              let uu____14130 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14130) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14122 in
                                          (uu____14121,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____14117 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14088 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14053 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14153 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14153 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14167 =
                                               let uu____14168 =
                                                 let uu____14172 =
                                                   let uu____14173 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14173 in
                                                 (uu____14172,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14168 in
                                             [uu____14167]
                                           else [] in
                                         let uu____14176 =
                                           let uu____14178 =
                                             let uu____14180 =
                                               let uu____14181 =
                                                 let uu____14185 =
                                                   let uu____14186 =
                                                     let uu____14192 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14192) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14186 in
                                                 (uu____14185, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14181 in
                                             [uu____14180] in
                                           FStar_List.append karr uu____14178 in
                                         FStar_List.append decls1 uu____14176 in
                                   let aux =
                                     let uu____14201 =
                                       let uu____14203 =
                                         inversion_axioms tapp vars in
                                       let uu____14205 =
                                         let uu____14207 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14207] in
                                       FStar_List.append uu____14203
                                         uu____14205 in
                                     FStar_List.append kindingAx uu____14201 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14212,uu____14213,uu____14214,uu____14215,uu____14216,uu____14217)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14224,t,uu____14226,n_tps,quals,uu____14229) ->
          let uu____14234 = new_term_constant_and_tok_from_lid env d in
          (match uu____14234 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14245 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14245 with
                | (formals,t_res) ->
                    let uu____14267 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14267 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14276 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14276 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14314 =
                                            mk_term_projector_name d x in
                                          (uu____14314,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14316 =
                                  let uu____14326 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14326, true) in
                                FStar_All.pipe_right uu____14316
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
                              let uu____14348 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14348 with
                               | (tok_typing,decls3) ->
                                   let uu____14355 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14355 with
                                    | (vars',guards',env'',decls_formals,uu____14370)
                                        ->
                                        let uu____14377 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14377 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14396 ->
                                                   let uu____14400 =
                                                     let uu____14401 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14401 in
                                                   [uu____14400] in
                                             let encode_elim uu____14408 =
                                               let uu____14409 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14409 with
                                               | (head1,args) ->
                                                   let uu____14438 =
                                                     let uu____14439 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14439.FStar_Syntax_Syntax.n in
                                                   (match uu____14438 with
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
                                                        let uu____14457 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14457
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
                                                                 | uu____14483
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14491
                                                                    =
                                                                    let uu____14492
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14492 in
                                                                    if
                                                                    uu____14491
                                                                    then
                                                                    let uu____14499
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14499]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14501
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14514
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14514
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14536
                                                                    =
                                                                    let uu____14540
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14540 in
                                                                    (match uu____14536
                                                                    with
                                                                    | 
                                                                    (uu____14547,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14553
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14553
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14555
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14555
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
                                                             (match uu____14501
                                                              with
                                                              | (uu____14563,arg_vars,elim_eqns_or_guards,uu____14566)
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
                                                                    let uu____14585
                                                                    =
                                                                    let uu____14589
                                                                    =
                                                                    let uu____14590
                                                                    =
                                                                    let uu____14596
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14602
                                                                    =
                                                                    let uu____14603
                                                                    =
                                                                    let uu____14606
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14606) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14603 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14596,
                                                                    uu____14602) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14590 in
                                                                    (uu____14589,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14585 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14619
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14619,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14621
                                                                    =
                                                                    let uu____14625
                                                                    =
                                                                    let uu____14626
                                                                    =
                                                                    let uu____14632
                                                                    =
                                                                    let uu____14635
                                                                    =
                                                                    let uu____14637
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14637] in
                                                                    [uu____14635] in
                                                                    let uu____14640
                                                                    =
                                                                    let uu____14641
                                                                    =
                                                                    let uu____14644
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14645
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14644,
                                                                    uu____14645) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14641 in
                                                                    (uu____14632,
                                                                    [x],
                                                                    uu____14640) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14626 in
                                                                    let uu____14655
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14625,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14655) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14621
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14660
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
                                                                    (let uu____14675
                                                                    =
                                                                    let uu____14676
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14676
                                                                    dapp1 in
                                                                    [uu____14675]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14660
                                                                    FStar_List.flatten in
                                                                    let uu____14680
                                                                    =
                                                                    let uu____14684
                                                                    =
                                                                    let uu____14685
                                                                    =
                                                                    let uu____14691
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14697
                                                                    =
                                                                    let uu____14698
                                                                    =
                                                                    let uu____14701
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14701) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14698 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14691,
                                                                    uu____14697) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14685 in
                                                                    (uu____14684,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14680) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14711 ->
                                                        ((let uu____14713 =
                                                            let uu____14714 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14715 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14714
                                                              uu____14715 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14713);
                                                         ([], []))) in
                                             let uu____14718 = encode_elim () in
                                             (match uu____14718 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14730 =
                                                      let uu____14732 =
                                                        let uu____14734 =
                                                          let uu____14736 =
                                                            let uu____14738 =
                                                              let uu____14739
                                                                =
                                                                let uu____14745
                                                                  =
                                                                  let uu____14747
                                                                    =
                                                                    let uu____14748
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14748 in
                                                                  Some
                                                                    uu____14747 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14745) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14739 in
                                                            [uu____14738] in
                                                          let uu____14751 =
                                                            let uu____14753 =
                                                              let uu____14755
                                                                =
                                                                let uu____14757
                                                                  =
                                                                  let uu____14759
                                                                    =
                                                                    let uu____14761
                                                                    =
                                                                    let uu____14763
                                                                    =
                                                                    let uu____14764
                                                                    =
                                                                    let uu____14768
                                                                    =
                                                                    let uu____14769
                                                                    =
                                                                    let uu____14775
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14775) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14769 in
                                                                    (uu____14768,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14764 in
                                                                    let uu____14782
                                                                    =
                                                                    let uu____14784
                                                                    =
                                                                    let uu____14785
                                                                    =
                                                                    let uu____14789
                                                                    =
                                                                    let uu____14790
                                                                    =
                                                                    let uu____14796
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14802
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14796,
                                                                    uu____14802) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14790 in
                                                                    (uu____14789,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14785 in
                                                                    [uu____14784] in
                                                                    uu____14763
                                                                    ::
                                                                    uu____14782 in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14761 in
                                                                  FStar_List.append
                                                                    uu____14759
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14757 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14755 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14753 in
                                                          FStar_List.append
                                                            uu____14736
                                                            uu____14751 in
                                                        FStar_List.append
                                                          decls3 uu____14734 in
                                                      FStar_List.append
                                                        decls2 uu____14732 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14730 in
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
           (fun uu____14823  ->
              fun se  ->
                match uu____14823 with
                | (g,env1) ->
                    let uu____14835 = encode_sigelt env1 se in
                    (match uu____14835 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14871 =
        match uu____14871 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14889 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14894 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14894
                   then
                     let uu____14895 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14896 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14897 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14895 uu____14896 uu____14897
                   else ());
                  (let uu____14899 = encode_term t1 env1 in
                   match uu____14899 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14909 =
                         let uu____14913 =
                           let uu____14914 =
                             let uu____14915 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____14915
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____14914 in
                         new_term_constant_from_string env1 x uu____14913 in
                       (match uu____14909 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____14926 = FStar_Options.log_queries () in
                              if uu____14926
                              then
                                let uu____14928 =
                                  let uu____14929 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____14930 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____14931 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14929 uu____14930 uu____14931 in
                                Some uu____14928
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14942,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____14951 = encode_free_var env1 fv t t_norm [] in
                 (match uu____14951 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____14970 = encode_sigelt env1 se in
                 (match uu____14970 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____14980 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____14980 with | (uu____14992,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15037  ->
            match uu____15037 with
            | (l,uu____15044,uu____15045) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15066  ->
            match uu____15066 with
            | (l,uu____15074,uu____15075) ->
                let uu____15080 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____15081 =
                  let uu____15083 =
                    let uu____15084 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15084 in
                  [uu____15083] in
                uu____15080 :: uu____15081)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15095 =
      let uu____15097 =
        let uu____15098 = FStar_Util.smap_create (Prims.parse_int "100") in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15098;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true
        } in
      [uu____15097] in
    FStar_ST.write last_env uu____15095
let get_env: FStar_TypeChecker_Env.env -> env_t =
  fun tcenv  ->
    let uu____15116 = FStar_ST.read last_env in
    match uu____15116 with
    | [] -> failwith "No env; call init first!"
    | e::uu____15122 ->
        let uu___161_15124 = e in
        {
          bindings = (uu___161_15124.bindings);
          depth = (uu___161_15124.depth);
          tcenv;
          warn = (uu___161_15124.warn);
          cache = (uu___161_15124.cache);
          nolabels = (uu___161_15124.nolabels);
          use_zfuel_name = (uu___161_15124.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___161_15124.encode_non_total_function_typ)
        }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15128 = FStar_ST.read last_env in
    match uu____15128 with
    | [] -> failwith "Empty env stack"
    | uu____15133::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15141  ->
    let uu____15142 = FStar_ST.read last_env in
    match uu____15142 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___162_15163 = hd1 in
          {
            bindings = (uu___162_15163.bindings);
            depth = (uu___162_15163.depth);
            tcenv = (uu___162_15163.tcenv);
            warn = (uu___162_15163.warn);
            cache = refs;
            nolabels = (uu___162_15163.nolabels);
            use_zfuel_name = (uu___162_15163.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_15163.encode_non_total_function_typ)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15169  ->
    let uu____15170 = FStar_ST.read last_env in
    match uu____15170 with
    | [] -> failwith "Popping an empty stack"
    | uu____15175::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15183  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15186  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15189  ->
    let uu____15190 = FStar_ST.read last_env in
    match uu____15190 with
    | hd1::uu____15196::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15202 -> failwith "Impossible"
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
        let uu____15247 = FStar_Options.log_queries () in
        if uu____15247
        then
          let uu____15249 =
            let uu____15250 =
              let uu____15251 =
                let uu____15252 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15252 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15251 in
            FStar_SMTEncoding_Term.Caption uu____15250 in
          uu____15249 :: decls
        else decls in
      let env = get_env tcenv in
      let uu____15259 = encode_sigelt env se in
      match uu____15259 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15265 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15265))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15276 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15276
       then
         let uu____15277 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15277
       else ());
      (let env = get_env tcenv in
       let uu____15282 =
         encode_signature
           (let uu___163_15286 = env in
            {
              bindings = (uu___163_15286.bindings);
              depth = (uu___163_15286.depth);
              tcenv = (uu___163_15286.tcenv);
              warn = false;
              cache = (uu___163_15286.cache);
              nolabels = (uu___163_15286.nolabels);
              use_zfuel_name = (uu___163_15286.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___163_15286.encode_non_total_function_typ)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15282 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15298 = FStar_Options.log_queries () in
             if uu____15298
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___164_15303 = env1 in
               {
                 bindings = (uu___164_15303.bindings);
                 depth = (uu___164_15303.depth);
                 tcenv = (uu___164_15303.tcenv);
                 warn = true;
                 cache = (uu___164_15303.cache);
                 nolabels = (uu___164_15303.nolabels);
                 use_zfuel_name = (uu___164_15303.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___164_15303.encode_non_total_function_typ)
               });
            (let uu____15305 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15305
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
        (let uu____15340 =
           let uu____15341 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15341.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15340);
        (let env = get_env tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15349 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15370 = aux rest in
                 (match uu____15370 with
                  | (out,rest1) ->
                      let t =
                        let uu____15388 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15388 with
                        | Some uu____15392 ->
                            let uu____15393 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15393
                              x.FStar_Syntax_Syntax.sort
                        | uu____15394 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15397 =
                        let uu____15399 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___165_15400 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___165_15400.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___165_15400.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15399 :: out in
                      (uu____15397, rest1))
             | uu____15403 -> ([], bindings1) in
           let uu____15407 = aux bindings in
           match uu____15407 with
           | (closing,bindings1) ->
               let uu____15421 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15421, bindings1) in
         match uu____15349 with
         | (q1,bindings1) ->
             let uu____15434 =
               let uu____15437 =
                 FStar_List.filter
                   (fun uu___134_15439  ->
                      match uu___134_15439 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15440 ->
                          false
                      | uu____15444 -> true) bindings1 in
               encode_env_bindings env uu____15437 in
             (match uu____15434 with
              | (env_decls,env1) ->
                  ((let uu____15455 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15455
                    then
                      let uu____15456 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15456
                    else ());
                   (let uu____15458 = encode_formula q1 env1 in
                    match uu____15458 with
                    | (phi,qdecls) ->
                        let uu____15470 =
                          let uu____15473 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15473 phi in
                        (match uu____15470 with
                         | (labels,phi1) ->
                             let uu____15483 = encode_labels labels in
                             (match uu____15483 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15504 =
                                      let uu____15508 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15509 =
                                        varops.mk_unique "@query" in
                                      (uu____15508, (Some "query"),
                                        uu____15509) in
                                    FStar_SMTEncoding_Term.Assume uu____15504 in
                                  let suffix =
                                    let uu____15513 =
                                      let uu____15515 =
                                        let uu____15517 =
                                          FStar_Options.print_z3_statistics
                                            () in
                                        if uu____15517
                                        then
                                          [FStar_SMTEncoding_Term.PrintStats]
                                        else [] in
                                      FStar_List.append uu____15515
                                        [FStar_SMTEncoding_Term.Echo "Done!"] in
                                    FStar_List.append label_suffix
                                      uu____15513 in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env = get_env tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15530 = encode_formula q env in
       match uu____15530 with
       | (f,uu____15534) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15536) -> true
             | uu____15539 -> false)))