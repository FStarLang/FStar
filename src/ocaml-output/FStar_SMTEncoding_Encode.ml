open Prims
let add_fuel x tl =
  let uu____16 = FStar_Options.unthrottle_inductives () in
  match uu____16 with | true  -> tl | uu____18 -> x :: tl
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___109_74  ->
       match uu___109_74 with
       | (FStar_Util.Inl uu____79,uu____80) -> false
       | uu____83 -> true) args
let subst_lcomp_opt s l =
  match l with
  | Some (FStar_Util.Inl l) ->
      let uu____114 =
        let uu____117 =
          let uu____118 =
            let uu____121 = l.FStar_Syntax_Syntax.comp () in
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
      let a =
        let uu___134_140 = a in
        let uu____141 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___134_140.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___134_140.FStar_Syntax_Syntax.sort)
        } in
      let uu____142 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
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
            let uu____157 = FStar_Util.string_of_int i in
            FStar_Util.format2
              "Projector %s on data constructor %s not found" uu____157
              lid.FStar_Ident.str in
          failwith uu____156 in
        let uu____158 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____158 with
        | (uu____161,t) ->
            let uu____163 =
              let uu____164 = FStar_Syntax_Subst.compress t in
              uu____164.FStar_Syntax_Syntax.n in
            (match uu____163 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____179 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____179 with
                  | (binders,uu____183) ->
                      (match (i < (Prims.parse_int "0")) ||
                               (i >= (FStar_List.length binders))
                       with
                       | true  -> fail ()
                       | uu____188 ->
                           let b = FStar_List.nth binders i in
                           mk_term_projector_name lid (Prims.fst b)))
             | uu____194 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____201 =
        let uu____202 = FStar_Util.string_of_int i in
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str uu____202 in
      FStar_All.pipe_left escape uu____201
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
  let new_scope uu____412 =
    let uu____413 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____415 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____413, uu____415) in
  let scopes =
    let uu____426 = let uu____432 = new_scope () in [uu____432] in
    FStar_Util.mk_ref uu____426 in
  let mk_unique y =
    let y = escape y in
    let y =
      let uu____457 =
        let uu____459 = FStar_ST.read scopes in
        FStar_Util.find_map uu____459
          (fun uu____476  ->
             match uu____476 with
             | (names,uu____483) -> FStar_Util.smap_try_find names y) in
      match uu____457 with
      | None  -> y
      | Some uu____488 ->
          (FStar_Util.incr ctr;
           (let uu____493 =
              let uu____494 =
                let uu____495 = FStar_ST.read ctr in
                FStar_Util.string_of_int uu____495 in
              Prims.strcat "__" uu____494 in
            Prims.strcat y uu____493)) in
    let top_scope =
      let uu____500 =
        let uu____505 = FStar_ST.read scopes in FStar_List.hd uu____505 in
      FStar_All.pipe_left Prims.fst uu____500 in
    FStar_Util.smap_add top_scope y true; y in
  let new_var pp rn =
    let uu____537 =
      let uu____538 =
        let uu____539 = FStar_Util.string_of_int rn in
        Prims.strcat "__" uu____539 in
      Prims.strcat pp.FStar_Ident.idText uu____538 in
    FStar_All.pipe_left mk_unique uu____537 in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id uu____547 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh pfx =
    let uu____558 =
      let uu____559 = next_id () in
      FStar_All.pipe_left FStar_Util.string_of_int uu____559 in
    FStar_Util.format2 "%s_%s" pfx uu____558 in
  let string_const s =
    let uu____564 =
      let uu____566 = FStar_ST.read scopes in
      FStar_Util.find_map uu____566
        (fun uu____583  ->
           match uu____583 with
           | (uu____589,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____564 with
    | Some f -> f
    | None  ->
        let id = next_id () in
        let f =
          let uu____598 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____598 in
        let top_scope =
          let uu____601 =
            let uu____606 = FStar_ST.read scopes in FStar_List.hd uu____606 in
          FStar_All.pipe_left Prims.snd uu____601 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push uu____634 =
    let uu____635 =
      let uu____641 = new_scope () in
      let uu____646 = FStar_ST.read scopes in uu____641 :: uu____646 in
    FStar_ST.write scopes uu____635 in
  let pop uu____673 =
    let uu____674 =
      let uu____680 = FStar_ST.read scopes in FStar_List.tl uu____680 in
    FStar_ST.write scopes uu____674 in
  let mark uu____707 = push () in
  let reset_mark uu____711 = pop () in
  let commit_mark uu____715 =
    let uu____716 = FStar_ST.read scopes in
    match uu____716 with
    | (hd1,hd2)::(next1,next2)::tl ->
        (FStar_Util.smap_fold hd1
           (fun key  ->
              fun value  -> fun v  -> FStar_Util.smap_add next1 key value) ();
         FStar_Util.smap_fold hd2
           (fun key  ->
              fun value  -> fun v  -> FStar_Util.smap_add next2 key value) ();
         FStar_ST.write scopes ((next1, next2) :: tl))
    | uu____776 -> failwith "Impossible" in
  {
    push;
    pop;
    mark;
    reset_mark;
    commit_mark;
    new_var;
    new_fvar;
    fresh;
    string_const;
    next_id;
    mk_unique
  }
let unmangle: FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu___135_785 = x in
    let uu____786 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____786;
      FStar_Syntax_Syntax.index = (uu___135_785.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___135_785.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term Prims.option* FStar_SMTEncoding_Term.term
  Prims.option)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____807 -> false
let __proj__Binding_var__item___0:
  binding -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____831 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident* Prims.string* FStar_SMTEncoding_Term.term
      Prims.option* FStar_SMTEncoding_Term.term Prims.option)
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar v = (v, None)
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
    let uu____950 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___110_954  ->
              match uu___110_954 with
              | Binding_var (x,uu____956) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____958,uu____959,uu____960) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____950 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option
  =
  fun env  ->
    fun t  ->
      let uu____993 = FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      match uu____993 with
      | true  ->
          let uu____995 = FStar_Syntax_Print.term_to_string t in
          Some uu____995
      | uu____996 -> None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1006 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1006)
let gen_term_var:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      let ysym =
        let uu____1017 = FStar_Util.string_of_int env.depth in
        Prims.strcat "@x" uu____1017 in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort) in
      (ysym, y,
        (let uu___136_1019 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___136_1019.tcenv);
           warn = (uu___136_1019.warn);
           cache = (uu___136_1019.cache);
           nolabels = (uu___136_1019.nolabels);
           use_zfuel_name = (uu___136_1019.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___136_1019.encode_non_total_function_typ)
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
        (let uu___137_1032 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___137_1032.depth);
           tcenv = (uu___137_1032.tcenv);
           warn = (uu___137_1032.warn);
           cache = (uu___137_1032.cache);
           nolabels = (uu___137_1032.nolabels);
           use_zfuel_name = (uu___137_1032.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___137_1032.encode_non_total_function_typ)
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
          (let uu___138_1048 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___138_1048.depth);
             tcenv = (uu___138_1048.tcenv);
             warn = (uu___138_1048.warn);
             cache = (uu___138_1048.cache);
             nolabels = (uu___138_1048.nolabels);
             use_zfuel_name = (uu___138_1048.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___138_1048.encode_non_total_function_typ)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___139_1058 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___139_1058.depth);
          tcenv = (uu___139_1058.tcenv);
          warn = (uu___139_1058.warn);
          cache = (uu___139_1058.cache);
          nolabels = (uu___139_1058.nolabels);
          use_zfuel_name = (uu___139_1058.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___139_1058.encode_non_total_function_typ)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___111_1074  ->
             match uu___111_1074 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1082 -> None) in
      let uu____1085 = aux a in
      match uu____1085 with
      | None  ->
          let a = unmangle a in
          let uu____1092 = aux a in
          (match uu____1092 with
           | None  ->
               let uu____1098 =
                 let uu____1099 = FStar_Syntax_Print.bv_to_string a in
                 FStar_Util.format1
                   "Bound term variable not found (after unmangling): %s"
                   uu____1099 in
               failwith uu____1098
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1119 =
        let uu___140_1120 = env in
        let uu____1121 =
          let uu____1123 =
            let uu____1124 =
              let uu____1131 =
                let uu____1133 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1133 in
              (x, fname, uu____1131, None) in
            Binding_fvar uu____1124 in
          uu____1123 :: (env.bindings) in
        {
          bindings = uu____1121;
          depth = (uu___140_1120.depth);
          tcenv = (uu___140_1120.tcenv);
          warn = (uu___140_1120.warn);
          cache = (uu___140_1120.cache);
          nolabels = (uu___140_1120.nolabels);
          use_zfuel_name = (uu___140_1120.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___140_1120.encode_non_total_function_typ)
        } in
      (fname, ftok, uu____1119)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___112_1155  ->
           match uu___112_1155 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1177 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1189 =
        lookup_binding env
          (fun uu___113_1191  ->
             match uu___113_1191 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1201 -> None) in
      FStar_All.pipe_right uu____1189 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1214 = try_lookup_lid env a in
      match uu____1214 with
      | None  ->
          let uu____1231 =
            let uu____1232 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1232 in
          failwith uu____1231
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
          let uu___141_1263 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___141_1263.depth);
            tcenv = (uu___141_1263.tcenv);
            warn = (uu___141_1263.warn);
            cache = (uu___141_1263.cache);
            nolabels = (uu___141_1263.nolabels);
            use_zfuel_name = (uu___141_1263.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___141_1263.encode_non_total_function_typ)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1275 = lookup_lid env x in
        match uu____1275 with
        | (t1,t2,uu____1283) ->
            let t3 =
              let uu____1289 =
                let uu____1293 =
                  let uu____1295 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1295] in
                (f, uu____1293) in
              FStar_SMTEncoding_Util.mkApp uu____1289 in
            let uu___142_1298 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___142_1298.depth);
              tcenv = (uu___142_1298.tcenv);
              warn = (uu___142_1298.warn);
              cache = (uu___142_1298.cache);
              nolabels = (uu___142_1298.nolabels);
              use_zfuel_name = (uu___142_1298.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___142_1298.encode_non_total_function_typ)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1308 = try_lookup_lid env l in
      match uu____1308 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1335 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1340,fuel::[]) ->
                         let uu____1343 =
                           let uu____1344 =
                             let uu____1345 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1345 Prims.fst in
                           FStar_Util.starts_with uu____1344 "fuel" in
                         (match uu____1343 with
                          | true  ->
                              let uu____1347 =
                                let uu____1348 =
                                  FStar_SMTEncoding_Util.mkFreeV
                                    (name, FStar_SMTEncoding_Term.Term_sort) in
                                FStar_SMTEncoding_Term.mk_ApplyTF uu____1348
                                  fuel in
                              FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                                uu____1347
                          | uu____1350 -> Some t)
                     | uu____1351 -> Some t)
                | uu____1352 -> None))
let lookup_free_var env a =
  let uu____1370 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1370 with
  | Some t -> t
  | None  ->
      let uu____1373 =
        let uu____1374 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1374 in
      failwith uu____1373
let lookup_free_var_name env a =
  let uu____1391 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1391 with | (x,uu____1398,uu____1399) -> x
let lookup_free_var_sym env a =
  let uu____1423 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1423 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1444;
             FStar_SMTEncoding_Term.rng = uu____1445;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1453 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym ->
                (match sym.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1467 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___114_1476  ->
           match uu___114_1476 with
           | Binding_fvar (uu____1478,nm',tok,uu____1481) when nm = nm' ->
               tok
           | uu____1486 -> None)
let mkForall_fuel' n uu____1503 =
  match uu____1503 with
  | (pats,vars,body) ->
      let fallback uu____1519 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1522 = FStar_Options.unthrottle_inductives () in
      (match uu____1522 with
       | true  -> fallback ()
       | uu____1523 ->
           let uu____1524 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
           (match uu____1524 with
            | (fsym,fterm) ->
                let add_fuel tms =
                  FStar_All.pipe_right tms
                    (FStar_List.map
                       (fun p  ->
                          match p.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.App
                              (FStar_SMTEncoding_Term.Var "HasType",args) ->
                              FStar_SMTEncoding_Util.mkApp
                                ("HasTypeFuel", (fterm :: args))
                          | uu____1543 -> p)) in
                let pats = FStar_List.map add_fuel pats in
                let body =
                  match body.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                      let guard =
                        match guard.FStar_SMTEncoding_Term.tm with
                        | FStar_SMTEncoding_Term.App
                            (FStar_SMTEncoding_Term.And ,guards) ->
                            let uu____1557 = add_fuel guards in
                            FStar_SMTEncoding_Util.mk_and_l uu____1557
                        | uu____1559 ->
                            let uu____1560 = add_fuel [guard] in
                            FStar_All.pipe_right uu____1560 FStar_List.hd in
                      FStar_SMTEncoding_Util.mkImp (guard, body')
                  | uu____1563 -> body in
                let vars = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars in
                FStar_SMTEncoding_Util.mkForall (pats, vars, body)))
let mkForall_fuel:
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list*
    FStar_SMTEncoding_Term.fvs* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = mkForall_fuel' (Prims.parse_int "1")
let head_normal: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t = FStar_Syntax_Util.unmeta t in
      match t.FStar_Syntax_Syntax.n with
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
          let uu____1607 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1607 FStar_Option.isNone
      | uu____1620 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1627 =
        let uu____1628 = FStar_Syntax_Util.un_uinst t in
        uu____1628.FStar_Syntax_Syntax.n in
      match uu____1627 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1631,uu____1632,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___115_1661  ->
                  match uu___115_1661 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1662 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1663,uu____1664,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1691 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1691 FStar_Option.isSome
      | uu____1704 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1711 = head_normal env t in
      match uu____1711 with
      | true  -> t
      | uu____1712 ->
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
    let uu____1722 =
      let uu____1726 = FStar_Syntax_Syntax.null_binder t in [uu____1726] in
    let uu____1727 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1722 uu____1727 None
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
                    let uu____1754 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1754
                | s ->
                    let uu____1757 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1757) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___116_1769  ->
    match uu___116_1769 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1770 -> false
let is_eta:
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term Prims.option
  =
  fun env  ->
    fun vars  ->
      fun t  ->
        let rec aux t xs =
          match ((t.FStar_SMTEncoding_Term.tm), xs) with
          | (FStar_SMTEncoding_Term.App
             (app,f::{
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV y;
                       FStar_SMTEncoding_Term.freevars = uu____1798;
                       FStar_SMTEncoding_Term.rng = uu____1799;_}::[]),x::xs)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              aux f xs
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1813) ->
              let uu____1818 =
                ((FStar_List.length args) = (FStar_List.length vars)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v
                          | uu____1828 -> false) args vars) in
              (match uu____1818 with
               | true  -> tok_of_name env f
               | uu____1830 -> None)
          | (uu____1831,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1834 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1836 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1836)) in
              (match uu____1834 with | true  -> Some t | uu____1838 -> None)
          | uu____1839 -> None in
        aux t (FStar_List.rev vars)
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
    | uu____1923 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___117_1926  ->
    match uu___117_1926 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____1928 =
          let uu____1932 =
            let uu____1934 =
              let uu____1935 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____1935 in
            [uu____1934] in
          ("FStar.Char.Char", uu____1932) in
        FStar_SMTEncoding_Util.mkApp uu____1928
    | FStar_Const.Const_int (i,None ) ->
        let uu____1943 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____1943
    | FStar_Const.Const_int (i,Some uu____1945) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____1954) ->
        let uu____1957 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____1957
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____1961 =
          let uu____1962 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____1962 in
        failwith uu____1961
let as_function_typ:
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t0  ->
      let rec aux norm t =
        let t = FStar_Syntax_Subst.compress t in
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____1981 -> t
        | FStar_Syntax_Syntax.Tm_refine uu____1989 ->
            let uu____1994 = FStar_Syntax_Util.unrefine t in
            aux true uu____1994
        | uu____1995 ->
            (match norm with
             | true  -> let uu____1996 = whnf env t in aux false uu____1996
             | uu____1997 ->
                 let uu____1998 =
                   let uu____1999 =
                     FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                   let uu____2000 = FStar_Syntax_Print.term_to_string t0 in
                   FStar_Util.format2 "(%s) Expected a function typ; got %s"
                     uu____1999 uu____2000 in
                 failwith uu____1998) in
      aux true t0
let curried_arrow_formals_comp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)
  =
  fun k  ->
    let k = FStar_Syntax_Subst.compress k in
    match k.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | uu____2021 ->
        let uu____2022 = FStar_Syntax_Syntax.mk_Total k in ([], uu____2022)
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
        (let uu____2165 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         match uu____2165 with
         | true  ->
             let uu____2166 = FStar_Syntax_Print.binders_to_string ", " bs in
             FStar_Util.print1 "Encoding binders %s\n" uu____2166
         | uu____2167 -> ());
        (let uu____2168 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2204  ->
                   fun b  ->
                     match uu____2204 with
                     | (vars,guards,env,decls,names) ->
                         let uu____2247 =
                           let x = unmangle (Prims.fst b) in
                           let uu____2256 = gen_term_var env x in
                           match uu____2256 with
                           | (xxsym,xx,env') ->
                               let uu____2270 =
                                 let uu____2273 =
                                   norm env x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2273 env xx in
                               (match uu____2270 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2247 with
                          | (v,g,env,decls',n) ->
                              ((v :: vars), (g :: guards), env,
                                (FStar_List.append decls decls'), (n ::
                                names)))) ([], [], env, [], [])) in
         match uu____2168 with
         | (vars,guards,env,decls,names) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env, decls,
               (FStar_List.rev names)))
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
          let uu____2361 = encode_term t env in
          match uu____2361 with
          | (t,decls) ->
              let uu____2368 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t in
              (uu____2368, decls)
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
          let uu____2376 = encode_term t env in
          match uu____2376 with
          | (t,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2385 = FStar_SMTEncoding_Term.mk_HasTypeZ e t in
                   (uu____2385, decls)
               | Some f ->
                   let uu____2387 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t in
                   (uu____2387, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2394 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       match uu____2394 with
       | true  ->
           let uu____2395 = FStar_Syntax_Print.tag_of_term t in
           let uu____2396 = FStar_Syntax_Print.tag_of_term t0 in
           let uu____2397 = FStar_Syntax_Print.term_to_string t0 in
           FStar_Util.print3 "(%s) (%s)   %s\n" uu____2395 uu____2396
             uu____2397
       | uu____2398 -> ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2402 =
             let uu____2403 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2404 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2405 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2406 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2403
               uu____2404 uu____2405 uu____2406 in
           failwith uu____2402
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2410 =
             let uu____2411 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2411 in
           failwith uu____2410
       | FStar_Syntax_Syntax.Tm_ascribed (t,k,uu____2416) ->
           encode_term t env
       | FStar_Syntax_Syntax.Tm_meta (t,uu____2436) -> encode_term t env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t = lookup_term_var env x in (t, [])
       | FStar_Syntax_Syntax.Tm_fvar v ->
           let uu____2445 = lookup_free_var env v.FStar_Syntax_Syntax.fv_name in
           (uu____2445, [])
       | FStar_Syntax_Syntax.Tm_type uu____2451 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t,uu____2454) -> encode_term t env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2460 = encode_const c in (uu____2460, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let uu____2474 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2474 with
            | (binders,res) ->
                let uu____2481 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                (match uu____2481 with
                 | true  ->
                     let uu____2484 = encode_binders None binders env in
                     (match uu____2484 with
                      | (vars,guards,env',decls,uu____2499) ->
                          let fsym =
                            let uu____2509 = varops.fresh "f" in
                            (uu____2509, FStar_SMTEncoding_Term.Term_sort) in
                          let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                          let app = mk_Apply f vars in
                          let uu____2512 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              (let uu___143_2516 = env.tcenv in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___143_2516.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___143_2516.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___143_2516.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___143_2516.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___143_2516.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___143_2516.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___143_2516.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___143_2516.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___143_2516.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___143_2516.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___143_2516.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___143_2516.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___143_2516.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___143_2516.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___143_2516.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___143_2516.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___143_2516.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___143_2516.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___143_2516.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___143_2516.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___143_2516.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___143_2516.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___143_2516.FStar_TypeChecker_Env.qname_and_index)
                               }) res in
                          (match uu____2512 with
                           | (pre_opt,res_t) ->
                               let uu____2523 =
                                 encode_term_pred None res_t env' app in
                               (match uu____2523 with
                                | (res_pred,decls') ->
                                    let uu____2530 =
                                      match pre_opt with
                                      | None  ->
                                          let uu____2537 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              guards in
                                          (uu____2537, [])
                                      | Some pre ->
                                          let uu____2540 =
                                            encode_formula pre env' in
                                          (match uu____2540 with
                                           | (guard,decls0) ->
                                               let uu____2548 =
                                                 FStar_SMTEncoding_Util.mk_and_l
                                                   (guard :: guards) in
                                               (uu____2548, decls0)) in
                                    (match uu____2530 with
                                     | (guards,guard_decls) ->
                                         let t_interp =
                                           let uu____2556 =
                                             let uu____2562 =
                                               FStar_SMTEncoding_Util.mkImp
                                                 (guards, res_pred) in
                                             ([[app]], vars, uu____2562) in
                                           FStar_SMTEncoding_Util.mkForall
                                             uu____2556 in
                                         let cvars =
                                           let uu____2572 =
                                             FStar_SMTEncoding_Term.free_variables
                                               t_interp in
                                           FStar_All.pipe_right uu____2572
                                             (FStar_List.filter
                                                (fun uu____2578  ->
                                                   match uu____2578 with
                                                   | (x,uu____2582) ->
                                                       x <> (Prims.fst fsym))) in
                                         let tkey =
                                           FStar_SMTEncoding_Util.mkForall
                                             ([], (fsym :: cvars), t_interp) in
                                         let tkey_hash =
                                           FStar_SMTEncoding_Term.hash_of_term
                                             tkey in
                                         let uu____2593 =
                                           FStar_Util.smap_try_find env.cache
                                             tkey_hash in
                                         (match uu____2593 with
                                          | Some (t',sorts,uu____2609) ->
                                              let uu____2619 =
                                                let uu____2620 =
                                                  let uu____2624 =
                                                    FStar_All.pipe_right
                                                      cvars
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV) in
                                                  (t', uu____2624) in
                                                FStar_SMTEncoding_Util.mkApp
                                                  uu____2620 in
                                              (uu____2619, [])
                                          | None  ->
                                              let tsym =
                                                let uu____2640 =
                                                  let uu____2641 =
                                                    FStar_Util.digest_of_string
                                                      tkey_hash in
                                                  Prims.strcat "Tm_arrow_"
                                                    uu____2641 in
                                                varops.mk_unique uu____2640 in
                                              let cvar_sorts =
                                                FStar_List.map Prims.snd
                                                  cvars in
                                              let caption =
                                                let uu____2648 =
                                                  FStar_Options.log_queries
                                                    () in
                                                match uu____2648 with
                                                | true  ->
                                                    let uu____2650 =
                                                      FStar_TypeChecker_Normalize.term_to_string
                                                        env.tcenv t0 in
                                                    Some uu____2650
                                                | uu____2651 -> None in
                                              let tdecl =
                                                FStar_SMTEncoding_Term.DeclFun
                                                  (tsym, cvar_sorts,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    caption) in
                                              let t =
                                                let uu____2656 =
                                                  let uu____2660 =
                                                    FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV
                                                      cvars in
                                                  (tsym, uu____2660) in
                                                FStar_SMTEncoding_Util.mkApp
                                                  uu____2656 in
                                              let t_has_kind =
                                                FStar_SMTEncoding_Term.mk_HasType
                                                  t
                                                  FStar_SMTEncoding_Term.mk_Term_type in
                                              let k_assumption =
                                                let a_name =
                                                  Some
                                                    (Prims.strcat "kinding_"
                                                       tsym) in
                                                let uu____2669 =
                                                  let uu____2674 =
                                                    FStar_SMTEncoding_Util.mkForall
                                                      ([[t_has_kind]], cvars,
                                                        t_has_kind) in
                                                  (uu____2674, a_name,
                                                    a_name) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____2669 in
                                              let f_has_t =
                                                FStar_SMTEncoding_Term.mk_HasType
                                                  f t in
                                              let f_has_t_z =
                                                FStar_SMTEncoding_Term.mk_HasTypeZ
                                                  f t in
                                              let pre_typing =
                                                let a_name =
                                                  Some
                                                    (Prims.strcat
                                                       "pre_typing_" tsym) in
                                                let uu____2689 =
                                                  let uu____2694 =
                                                    let uu____2695 =
                                                      let uu____2701 =
                                                        let uu____2702 =
                                                          let uu____2705 =
                                                            let uu____2706 =
                                                              FStar_SMTEncoding_Term.mk_PreType
                                                                f in
                                                            FStar_SMTEncoding_Term.mk_tester
                                                              "Tm_arrow"
                                                              uu____2706 in
                                                          (f_has_t,
                                                            uu____2705) in
                                                        FStar_SMTEncoding_Util.mkImp
                                                          uu____2702 in
                                                      ([[f_has_t]], (fsym ::
                                                        cvars), uu____2701) in
                                                    mkForall_fuel uu____2695 in
                                                  (uu____2694,
                                                    (Some
                                                       "pre-typing for functions"),
                                                    a_name) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____2689 in
                                              let t_interp =
                                                let a_name =
                                                  Some
                                                    (Prims.strcat
                                                       "interpretation_" tsym) in
                                                let uu____2721 =
                                                  let uu____2726 =
                                                    let uu____2727 =
                                                      let uu____2733 =
                                                        FStar_SMTEncoding_Util.mkIff
                                                          (f_has_t_z,
                                                            t_interp) in
                                                      ([[f_has_t_z]], (fsym
                                                        :: cvars),
                                                        uu____2733) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____2727 in
                                                  (uu____2726, a_name,
                                                    a_name) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____2721 in
                                              let t_decls =
                                                FStar_List.append (tdecl ::
                                                  decls)
                                                  (FStar_List.append decls'
                                                     (FStar_List.append
                                                        guard_decls
                                                        [k_assumption;
                                                        pre_typing;
                                                        t_interp])) in
                                              (FStar_Util.smap_add env.cache
                                                 tkey_hash
                                                 (tsym, cvar_sorts, t_decls);
                                               (t, t_decls)))))))
                 | uu____2756 ->
                     let tsym = varops.fresh "Non_total_Tm_arrow" in
                     let tdecl =
                       FStar_SMTEncoding_Term.DeclFun
                         (tsym, [], FStar_SMTEncoding_Term.Term_sort, None) in
                     let t = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                     let t_kinding =
                       let a_name =
                         Some
                           (Prims.strcat "non_total_function_typing_" tsym) in
                       let uu____2766 =
                         let uu____2771 =
                           FStar_SMTEncoding_Term.mk_HasType t
                             FStar_SMTEncoding_Term.mk_Term_type in
                         (uu____2771, (Some "Typing for non-total arrows"),
                           a_name) in
                       FStar_SMTEncoding_Term.Assume uu____2766 in
                     let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                     let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                     let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t in
                     let t_interp =
                       let a_name = Some (Prims.strcat "pre_typing_" tsym) in
                       let uu____2782 =
                         let uu____2787 =
                           let uu____2788 =
                             let uu____2794 =
                               let uu____2795 =
                                 let uu____2798 =
                                   let uu____2799 =
                                     FStar_SMTEncoding_Term.mk_PreType f in
                                   FStar_SMTEncoding_Term.mk_tester
                                     "Tm_arrow" uu____2799 in
                                 (f_has_t, uu____2798) in
                               FStar_SMTEncoding_Util.mkImp uu____2795 in
                             ([[f_has_t]], [fsym], uu____2794) in
                           mkForall_fuel uu____2788 in
                         (uu____2787, a_name, a_name) in
                       FStar_SMTEncoding_Term.Assume uu____2782 in
                     (t, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2814 ->
           let uu____2819 =
             let uu____2822 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2822 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2827;
                 FStar_Syntax_Syntax.pos = uu____2828;
                 FStar_Syntax_Syntax.vars = uu____2829;_} ->
                 let uu____2836 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2836 with
                  | (b,f) ->
                      let uu____2850 =
                        let uu____2851 = FStar_List.hd b in
                        Prims.fst uu____2851 in
                      (uu____2850, f))
             | uu____2856 -> failwith "impossible" in
           (match uu____2819 with
            | (x,f) ->
                let uu____2863 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____2863 with
                 | (base_t,decls) ->
                     let uu____2870 = gen_term_var env x in
                     (match uu____2870 with
                      | (x,xtm,env') ->
                          let uu____2879 = encode_formula f env' in
                          (match uu____2879 with
                           | (refinement,decls') ->
                               let uu____2886 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____2886 with
                                | (fsym,fterm) ->
                                    let encoding =
                                      let uu____2894 =
                                        let uu____2897 =
                                          FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                            (Some fterm) xtm base_t in
                                        (uu____2897, refinement) in
                                      FStar_SMTEncoding_Util.mkAnd uu____2894 in
                                    let cvars =
                                      let uu____2902 =
                                        FStar_SMTEncoding_Term.free_variables
                                          encoding in
                                      FStar_All.pipe_right uu____2902
                                        (FStar_List.filter
                                           (fun uu____2908  ->
                                              match uu____2908 with
                                              | (y,uu____2912) ->
                                                  (y <> x) && (y <> fsym))) in
                                    let xfv =
                                      (x, FStar_SMTEncoding_Term.Term_sort) in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort) in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars), encoding) in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey in
                                    let uu____2931 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2931 with
                                     | Some (t,uu____2946,uu____2947) ->
                                         let uu____2957 =
                                           let uu____2958 =
                                             let uu____2962 =
                                               FStar_All.pipe_right cvars
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             (t, uu____2962) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2958 in
                                         (uu____2957, [])
                                     | None  ->
                                         let tsym =
                                           let uu____2978 =
                                             let uu____2979 =
                                               FStar_Util.digest_of_string
                                                 tkey_hash in
                                             Prims.strcat "Tm_refine_"
                                               uu____2979 in
                                           varops.mk_unique uu____2978 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t =
                                           let uu____2988 =
                                             let uu____2992 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars in
                                             (tsym, uu____2992) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2988 in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (Some fterm) xtm t in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t
                                             FStar_SMTEncoding_Term.mk_Term_type in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t in
                                         let t_haseq =
                                           let uu____3002 =
                                             let uu____3007 =
                                               let uu____3008 =
                                                 let uu____3014 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars,
                                                   uu____3014) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3008 in
                                             (uu____3007,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Some
                                                  (Prims.strcat "haseq" tsym))) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3002 in
                                         let t_kinding =
                                           let uu____3025 =
                                             let uu____3030 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars,
                                                   t_has_kind) in
                                             (uu____3030,
                                               (Some "refinement kinding"),
                                               (Some
                                                  (Prims.strcat
                                                     "refinement_kinding_"
                                                     tsym))) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3025 in
                                         let t_interp =
                                           let uu____3041 =
                                             let uu____3046 =
                                               let uu____3047 =
                                                 let uu____3053 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars), uu____3053) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3047 in
                                             let uu____3065 =
                                               let uu____3067 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3067 in
                                             (uu____3046, uu____3065,
                                               (Some
                                                  (Prims.strcat
                                                     "refinement_interpretation_"
                                                     tsym))) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3041 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq]) in
                                         (FStar_Util.smap_add env.cache
                                            tkey_hash
                                            (tsym, cvar_sorts, t_decls);
                                          (t, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3096 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3096 in
           let uu____3100 = encode_term_pred None k env ttm in
           (match uu____3100 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3108 =
                    let uu____3113 =
                      let uu____3115 =
                        let uu____3116 =
                          let uu____3117 =
                            let uu____3118 = FStar_Unionfind.uvar_id uv in
                            FStar_All.pipe_left FStar_Util.string_of_int
                              uu____3118 in
                          FStar_Util.format1 "uvar_typing_%s" uu____3117 in
                        varops.mk_unique uu____3116 in
                      Some uu____3115 in
                    (t_has_k, (Some "Uvar typing"), uu____3113) in
                  FStar_SMTEncoding_Term.Assume uu____3108 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3125 ->
           let uu____3135 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3135 with
            | (head,args_e) ->
                let uu____3163 =
                  let uu____3171 =
                    let uu____3172 = FStar_Syntax_Subst.compress head in
                    uu____3172.FStar_Syntax_Syntax.n in
                  (uu____3171, args_e) in
                (match uu____3163 with
                 | (uu____3182,uu____3183) when head_redex env head ->
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
                      | (v1,decls1) ->
                          let uu____3275 = encode_term v2 env in
                          (match uu____3275 with
                           | (v2,decls2) ->
                               let uu____3282 =
                                 FStar_SMTEncoding_Util.mk_LexCons v1 v2 in
                               (uu____3282,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3284::uu____3285::uu____3286) ->
                     let e0 =
                       let uu____3316 =
                         let uu____3319 =
                           let uu____3320 =
                             let uu____3330 =
                               let uu____3336 = FStar_List.hd args_e in
                               [uu____3336] in
                             (head, uu____3330) in
                           FStar_Syntax_Syntax.Tm_app uu____3320 in
                         FStar_Syntax_Syntax.mk uu____3319 in
                       uu____3316 None head.FStar_Syntax_Syntax.pos in
                     let e =
                       let uu____3371 =
                         let uu____3374 =
                           let uu____3375 =
                             let uu____3385 = FStar_List.tl args_e in
                             (e0, uu____3385) in
                           FStar_Syntax_Syntax.Tm_app uu____3375 in
                         FStar_Syntax_Syntax.mk uu____3374 in
                       uu____3371 None t0.FStar_Syntax_Syntax.pos in
                     encode_term e env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),(arg,uu____3411)::[]) ->
                     let uu____3429 = encode_term arg env in
                     (match uu____3429 with
                      | (tm,decls) ->
                          let uu____3436 =
                            FStar_SMTEncoding_Util.mkApp ("Reify", [tm]) in
                          (uu____3436, decls))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3438),(arg,uu____3440)::[]) -> encode_term arg env
                 | uu____3458 ->
                     let uu____3466 = encode_args args_e env in
                     (match uu____3466 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3499 = encode_term head env in
                            match uu____3499 with
                            | (head,decls') ->
                                let app_tm = mk_Apply_args head args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3538 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3538 with
                                      | (formals,rest) ->
                                          let subst =
                                            FStar_List.map2
                                              (fun uu____3580  ->
                                                 fun uu____3581  ->
                                                   match (uu____3580,
                                                           uu____3581)
                                                   with
                                                   | ((bv,uu____3595),
                                                      (a,uu____3597)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals
                                              args_e in
                                          let ty =
                                            let uu____3611 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3611
                                              (FStar_Syntax_Subst.subst subst) in
                                          let uu____3616 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3616 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3626 =
                                                   let uu____3631 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3636 =
                                                     let uu____3638 =
                                                       let uu____3639 =
                                                         let uu____3640 =
                                                           let uu____3641 =
                                                             FStar_SMTEncoding_Term.hash_of_term
                                                               app_tm in
                                                           FStar_Util.digest_of_string
                                                             uu____3641 in
                                                         Prims.strcat
                                                           "partial_app_typing_"
                                                           uu____3640 in
                                                       varops.mk_unique
                                                         uu____3639 in
                                                     Some uu____3638 in
                                                   (uu____3631,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3636) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3626 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3659 = lookup_free_var_sym env fv in
                            match uu____3659 with
                            | (fname,fuel_args) ->
                                let tm =
                                  FStar_SMTEncoding_Util.mkApp'
                                    (fname,
                                      (FStar_List.append fuel_args args)) in
                                (tm, decls) in
                          let head = FStar_Syntax_Subst.compress head in
                          let head_type =
                            match head.FStar_Syntax_Syntax.n with
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
                                let uu____3697 =
                                  let uu____3698 =
                                    FStar_TypeChecker_Env.lookup_lid
                                      env.tcenv
                                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                  FStar_All.pipe_right uu____3698 Prims.snd in
                                Some uu____3697
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3707,FStar_Util.Inl t,uu____3709) ->
                                Some t
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3730,FStar_Util.Inr c,uu____3732) ->
                                Some (FStar_Syntax_Util.comp_result c)
                            | uu____3753 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type ->
                               let head_type =
                                 let uu____3773 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3773 in
                               let uu____3774 =
                                 curried_arrow_formals_comp head_type in
                               (match uu____3774 with
                                | (formals,c) ->
                                    (match head.FStar_Syntax_Syntax.n with
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
                                     | uu____3799 ->
                                         (match (FStar_List.length formals) >
                                                  (FStar_List.length args)
                                          with
                                          | true  ->
                                              encode_partial_app
                                                (Some (formals, c))
                                          | uu____3811 ->
                                              encode_partial_app None)))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3844 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3844 with
            | (bs,body,opening) ->
                let fallback uu____3859 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3864 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3864, [decl]) in
                let is_impure uu___118_3874 =
                  match uu___118_3874 with
                  | FStar_Util.Inl lc ->
                      let uu____3884 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc in
                      Prims.op_Negation uu____3884
                  | FStar_Util.Inr (eff,uu____3886) ->
                      let uu____3892 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3892 Prims.op_Negation in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc ->
                      let uu____3913 =
                        let uu____3914 = lc.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____3914 in
                      FStar_All.pipe_right uu____3913
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar uu____3926 =
                        let uu____3927 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____3927 Prims.fst in
                      (match FStar_Ident.lid_equals eff
                               FStar_Syntax_Const.effect_Tot_lid
                       with
                       | true  ->
                           let uu____3935 =
                             let uu____3936 = new_uvar () in
                             FStar_Syntax_Syntax.mk_Total uu____3936 in
                           FStar_All.pipe_right uu____3935
                             (fun _0_32  -> Some _0_32)
                       | uu____3938 ->
                           (match FStar_Ident.lid_equals eff
                                    FStar_Syntax_Const.effect_GTot_lid
                            with
                            | true  ->
                                let uu____3940 =
                                  let uu____3941 = new_uvar () in
                                  FStar_Syntax_Syntax.mk_GTotal uu____3941 in
                                FStar_All.pipe_right uu____3940
                                  (fun _0_33  -> Some _0_33)
                            | uu____3943 -> None)) in
                (match lopt with
                 | None  ->
                     ((let uu____3952 =
                         let uu____3953 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s"
                           uu____3953 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____3952);
                      fallback ())
                 | Some lc ->
                     let uu____3965 = is_impure lc in
                     (match uu____3965 with
                      | true  -> fallback ()
                      | uu____3968 ->
                          let uu____3969 = encode_binders None bs env in
                          (match uu____3969 with
                           | (vars,guards,envbody,decls,uu____3984) ->
                               let uu____3991 = encode_term body envbody in
                               (match uu____3991 with
                                | (body,decls') ->
                                    let key_body =
                                      let uu____3999 =
                                        let uu____4005 =
                                          let uu____4006 =
                                            let uu____4009 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                guards in
                                            (uu____4009, body) in
                                          FStar_SMTEncoding_Util.mkImp
                                            uu____4006 in
                                        ([], vars, uu____4005) in
                                      FStar_SMTEncoding_Util.mkForall
                                        uu____3999 in
                                    let cvars =
                                      FStar_SMTEncoding_Term.free_variables
                                        key_body in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], cvars, key_body) in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey in
                                    let uu____4020 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____4020 with
                                     | Some (t,uu____4035,uu____4036) ->
                                         let uu____4046 =
                                           let uu____4047 =
                                             let uu____4051 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars in
                                             (t, uu____4051) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4047 in
                                         (uu____4046, [])
                                     | None  ->
                                         let uu____4062 =
                                           is_eta env vars body in
                                         (match uu____4062 with
                                          | Some t -> (t, [])
                                          | None  ->
                                              let cvar_sorts =
                                                FStar_List.map Prims.snd
                                                  cvars in
                                              let fsym =
                                                let uu____4073 =
                                                  let uu____4074 =
                                                    FStar_Util.digest_of_string
                                                      tkey_hash in
                                                  Prims.strcat "Tm_abs_"
                                                    uu____4074 in
                                                varops.mk_unique uu____4073 in
                                              let fdecl =
                                                FStar_SMTEncoding_Term.DeclFun
                                                  (fsym, cvar_sorts,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    None) in
                                              let f =
                                                let uu____4079 =
                                                  let uu____4083 =
                                                    FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV
                                                      cvars in
                                                  (fsym, uu____4083) in
                                                FStar_SMTEncoding_Util.mkApp
                                                  uu____4079 in
                                              let app = mk_Apply f vars in
                                              let typing_f =
                                                let uu____4091 =
                                                  codomain_eff lc in
                                                match uu____4091 with
                                                | None  -> []
                                                | Some c ->
                                                    let tfun =
                                                      FStar_Syntax_Util.arrow
                                                        bs c in
                                                    let uu____4098 =
                                                      encode_term_pred None
                                                        tfun env f in
                                                    (match uu____4098 with
                                                     | (f_has_t,decls'') ->
                                                         let a_name =
                                                           Some
                                                             (Prims.strcat
                                                                "typing_"
                                                                fsym) in
                                                         let uu____4106 =
                                                           let uu____4108 =
                                                             let uu____4109 =
                                                               let uu____4114
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars,
                                                                    f_has_t) in
                                                               (uu____4114,
                                                                 a_name,
                                                                 a_name) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____4109 in
                                                           [uu____4108] in
                                                         FStar_List.append
                                                           decls'' uu____4106) in
                                              let interp_f =
                                                let a_name =
                                                  Some
                                                    (Prims.strcat
                                                       "interpretation_" fsym) in
                                                let uu____4124 =
                                                  let uu____4129 =
                                                    let uu____4130 =
                                                      let uu____4136 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (app, body) in
                                                      ([[app]],
                                                        (FStar_List.append
                                                           vars cvars),
                                                        uu____4136) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____4130 in
                                                  (uu____4129, a_name,
                                                    a_name) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____4124 in
                                              let f_decls =
                                                FStar_List.append decls
                                                  (FStar_List.append decls'
                                                     (FStar_List.append
                                                        (fdecl :: typing_f)
                                                        [interp_f])) in
                                              (FStar_Util.smap_add env.cache
                                                 tkey_hash
                                                 (fsym, cvar_sorts, f_decls);
                                               (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4155,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4156;
                          FStar_Syntax_Syntax.lbunivs = uu____4157;
                          FStar_Syntax_Syntax.lbtyp = uu____4158;
                          FStar_Syntax_Syntax.lbeff = uu____4159;
                          FStar_Syntax_Syntax.lbdef = uu____4160;_}::uu____4161),uu____4162)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4180;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4182;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4198 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4211 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4211, [decl_e])))
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
              let uu____4253 = encode_term e1 env in
              match uu____4253 with
              | (ee1,decls1) ->
                  let uu____4260 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4260 with
                   | (xs,e2) ->
                       let uu____4274 = FStar_List.hd xs in
                       (match uu____4274 with
                        | (x,uu____4282) ->
                            let env' = push_term_var env x ee1 in
                            let uu____4284 = encode_body e2 env' in
                            (match uu____4284 with
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
            let uu____4306 = encode_term e env in
            match uu____4306 with
            | (scr,decls) ->
                let uu____4313 =
                  FStar_List.fold_right
                    (fun b  ->
                       fun uu____4321  ->
                         match uu____4321 with
                         | (else_case,decls) ->
                             let uu____4332 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4332 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env p in
                                  FStar_List.fold_right
                                    (fun uu____4362  ->
                                       fun uu____4363  ->
                                         match (uu____4362, uu____4363) with
                                         | ((env0,pattern),(else_case,decls))
                                             ->
                                             let guard = pattern.guard scr in
                                             let projections =
                                               pattern.projections scr in
                                             let env =
                                               FStar_All.pipe_right
                                                 projections
                                                 (FStar_List.fold_left
                                                    (fun env  ->
                                                       fun uu____4400  ->
                                                         match uu____4400
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env x t) env) in
                                             let uu____4405 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w ->
                                                   let uu____4420 =
                                                     encode_term w env in
                                                   (match uu____4420 with
                                                    | (w,decls2) ->
                                                        let uu____4428 =
                                                          let uu____4429 =
                                                            let uu____4432 =
                                                              let uu____4433
                                                                =
                                                                let uu____4436
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w,
                                                                  uu____4436) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4433 in
                                                            (guard,
                                                              uu____4432) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4429 in
                                                        (uu____4428, decls2)) in
                                             (match uu____4405 with
                                              | (guard,decls2) ->
                                                  let uu____4444 =
                                                    encode_br br env in
                                                  (match uu____4444 with
                                                   | (br,decls3) ->
                                                       let uu____4452 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard, br,
                                                             else_case) in
                                                       (uu____4452,
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls2 decls3))))))
                                    patterns (else_case, decls))) pats
                    (default_case, decls) in
                (match uu____4313 with
                 | (match_tm,decls) -> (match_tm, decls))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4476 -> let uu____4477 = encode_one_pat env pat in [uu____4477]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4489 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       match uu____4489 with
       | true  ->
           let uu____4490 = FStar_Syntax_Print.pat_to_string pat in
           FStar_Util.print1 "Encoding pattern %s\n" uu____4490
       | uu____4491 -> ());
      (let uu____4492 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4492 with
       | (vars,pat_term) ->
           let uu____4502 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4525  ->
                     fun v  ->
                       match uu____4525 with
                       | (env,vars) ->
                           let uu____4553 = gen_term_var env v in
                           (match uu____4553 with
                            | (xx,uu____4565,env) ->
                                (env,
                                  ((v,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars)))) (env, [])) in
           (match uu____4502 with
            | (env,vars) ->
                let rec mk_guard pat scrutinee =
                  match pat.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4612 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4620 =
                        let uu____4623 = encode_const c in
                        (scrutinee, uu____4623) in
                      FStar_SMTEncoding_Util.mkEq uu____4620
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        mk_data_tester env
                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4654  ->
                                  match uu____4654 with
                                  | (arg,uu____4660) ->
                                      let proj =
                                        primitive_projector_by_pos env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4670 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4670)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat scrutinee =
                  match pat.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4689 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4704 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4719 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4741  ->
                                  match uu____4741 with
                                  | (arg,uu____4750) ->
                                      let proj =
                                        primitive_projector_by_pos env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4760 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____4760)) in
                      FStar_All.pipe_right uu____4719 FStar_List.flatten in
                let pat_term uu____4776 = encode_term pat_term env in
                let pattern =
                  {
                    pat_vars = vars;
                    pat_term;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  } in
                (env, pattern)))
and encode_args:
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list*
        FStar_SMTEncoding_Term.decls_t)
  =
  fun l  ->
    fun env  ->
      let uu____4783 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____4798  ->
                fun uu____4799  ->
                  match (uu____4798, uu____4799) with
                  | ((tms,decls),(t,uu____4819)) ->
                      let uu____4830 = encode_term t env in
                      (match uu____4830 with
                       | (t,decls') ->
                           ((t :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____4783 with | (l,decls) -> ((FStar_List.rev l), decls)
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
          let list_elements e =
            let uu____4868 = FStar_Syntax_Util.list_elements e in
            match uu____4868 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 []) in
          let one_pat p =
            let uu____4886 =
              let uu____4896 = FStar_Syntax_Util.unmeta p in
              FStar_All.pipe_right uu____4896 FStar_Syntax_Util.head_and_args in
            match uu____4886 with
            | (head,args) ->
                let uu____4927 =
                  let uu____4935 =
                    let uu____4936 = FStar_Syntax_Util.un_uinst head in
                    uu____4936.FStar_Syntax_Syntax.n in
                  (uu____4935, args) in
                (match uu____4927 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____4950,uu____4951)::(e,uu____4953)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____4984)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5005 -> failwith "Unexpected pattern term") in
          let lemma_pats p =
            let elts = list_elements p in
            let smt_pat_or t =
              let uu____5038 =
                let uu____5048 = FStar_Syntax_Util.unmeta t in
                FStar_All.pipe_right uu____5048
                  FStar_Syntax_Util.head_and_args in
              match uu____5038 with
              | (head,args) ->
                  let uu____5077 =
                    let uu____5085 =
                      let uu____5086 = FStar_Syntax_Util.un_uinst head in
                      uu____5086.FStar_Syntax_Syntax.n in
                    (uu____5085, args) in
                  (match uu____5077 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5099)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5119 -> None) in
            match elts with
            | t::[] ->
                let uu____5137 = smt_pat_or t in
                (match uu____5137 with
                 | Some e ->
                     let uu____5153 = list_elements e in
                     FStar_All.pipe_right uu____5153
                       (FStar_List.map
                          (fun branch  ->
                             let uu____5170 = list_elements branch in
                             FStar_All.pipe_right uu____5170
                               (FStar_List.map one_pat)))
                 | uu____5184 ->
                     let uu____5188 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat) in
                     [uu____5188])
            | uu____5219 ->
                let uu____5221 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat) in
                [uu____5221] in
          let uu____5252 =
            let uu____5268 =
              let uu____5269 = FStar_Syntax_Subst.compress t in
              uu____5269.FStar_Syntax_Syntax.n in
            match uu____5268 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5299 = FStar_Syntax_Subst.open_comp binders c in
                (match uu____5299 with
                 | (binders,c) ->
                     (match c.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5334;
                            FStar_Syntax_Syntax.effect_name = uu____5335;
                            FStar_Syntax_Syntax.result_typ = uu____5336;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5338)::(post,uu____5340)::(pats,uu____5342)::[];
                            FStar_Syntax_Syntax.flags = uu____5343;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats in
                          let uu____5377 = lemma_pats pats' in
                          (binders, pre, post, uu____5377)
                      | uu____5396 -> failwith "impos"))
            | uu____5412 -> failwith "Impos" in
          match uu____5252 with
          | (binders,pre,post,patterns) ->
              let uu____5456 = encode_binders None binders env in
              (match uu____5456 with
               | (vars,guards,env,decls,uu____5471) ->
                   let uu____5478 =
                     let uu____5485 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch  ->
                               let uu____5516 =
                                 let uu____5521 =
                                   FStar_All.pipe_right branch
                                     (FStar_List.map
                                        (fun uu____5537  ->
                                           match uu____5537 with
                                           | (t,uu____5544) ->
                                               encode_term t
                                                 (let uu___144_5547 = env in
                                                  {
                                                    bindings =
                                                      (uu___144_5547.bindings);
                                                    depth =
                                                      (uu___144_5547.depth);
                                                    tcenv =
                                                      (uu___144_5547.tcenv);
                                                    warn =
                                                      (uu___144_5547.warn);
                                                    cache =
                                                      (uu___144_5547.cache);
                                                    nolabels =
                                                      (uu___144_5547.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___144_5547.encode_non_total_function_typ)
                                                  }))) in
                                 FStar_All.pipe_right uu____5521
                                   FStar_List.unzip in
                               match uu____5516 with
                               | (pats,decls) -> (pats, decls))) in
                     FStar_All.pipe_right uu____5485 FStar_List.unzip in
                   (match uu____5478 with
                    | (pats,decls') ->
                        let decls' = FStar_List.flatten decls' in
                        let pats =
                          match induction_on with
                          | None  -> pats
                          | Some e ->
                              (match vars with
                               | [] -> pats
                               | l::[] ->
                                   FStar_All.pipe_right pats
                                     (FStar_List.map
                                        (fun p  ->
                                           let uu____5611 =
                                             let uu____5612 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5612 e in
                                           uu____5611 :: p))
                               | uu____5613 ->
                                   let rec aux tl vars =
                                     match vars with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5642 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl e in
                                                 uu____5642 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars
                                         ->
                                         let uu____5650 =
                                           let uu____5651 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort) in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5651 tl in
                                         aux uu____5650 vars
                                     | uu____5652 -> pats in
                                   let uu____5656 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort) in
                                   aux uu____5656 vars) in
                        let env =
                          let uu___145_5658 = env in
                          {
                            bindings = (uu___145_5658.bindings);
                            depth = (uu___145_5658.depth);
                            tcenv = (uu___145_5658.tcenv);
                            warn = (uu___145_5658.warn);
                            cache = (uu___145_5658.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___145_5658.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___145_5658.encode_non_total_function_typ)
                          } in
                        let uu____5659 =
                          let uu____5662 = FStar_Syntax_Util.unmeta pre in
                          encode_formula uu____5662 env in
                        (match uu____5659 with
                         | (pre,decls'') ->
                             let uu____5667 =
                               let uu____5670 = FStar_Syntax_Util.unmeta post in
                               encode_formula uu____5670 env in
                             (match uu____5667 with
                              | (post,decls''') ->
                                  let decls =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls')
                                         (FStar_List.append decls'' decls''')) in
                                  let uu____5677 =
                                    let uu____5678 =
                                      let uu____5684 =
                                        let uu____5685 =
                                          let uu____5688 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre :: guards) in
                                          (uu____5688, post) in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5685 in
                                      (pats, vars, uu____5684) in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5678 in
                                  (uu____5677, decls)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug phi =
        let uu____5701 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        match uu____5701 with
        | true  ->
            let uu____5702 = FStar_Syntax_Print.tag_of_term phi in
            let uu____5703 = FStar_Syntax_Print.term_to_string phi in
            FStar_Util.print2 "Formula (%s)  %s\n" uu____5702 uu____5703
        | uu____5704 -> () in
      let enc f r l =
        let uu____5730 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5743 = encode_term (Prims.fst x) env in
                 match uu____5743 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5730 with
        | (decls,args) ->
            let uu____5760 =
              let uu___146_5761 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___146_5761.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___146_5761.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5760, decls) in
      let const_op f r uu____5780 = let uu____5783 = f r in (uu____5783, []) in
      let un_op f l =
        let uu____5799 = FStar_List.hd l in FStar_All.pipe_left f uu____5799 in
      let bin_op f uu___119_5812 =
        match uu___119_5812 with
        | t1::t2::[] -> f (t1, t2)
        | uu____5820 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____5847 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____5856  ->
                 match uu____5856 with
                 | (t,uu____5864) ->
                     let uu____5865 = encode_formula t env in
                     (match uu____5865 with
                      | (phi,decls') ->
                          ((FStar_List.append decls decls'), phi))) [] l in
        match uu____5847 with
        | (decls,phis) ->
            let uu____5882 =
              let uu___147_5883 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___147_5883.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___147_5883.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5882, decls) in
      let eq_op r uu___120_5899 =
        match uu___120_5899 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____5959 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____5959 r [e1; e2]
        | l ->
            let uu____5979 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____5979 r l in
      let mk_imp r uu___121_5998 =
        match uu___121_5998 with
        | (lhs,uu____6002)::(rhs,uu____6004)::[] ->
            let uu____6025 = encode_formula rhs env in
            (match uu____6025 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6034) ->
                      (l1, decls1)
                  | uu____6037 ->
                      let uu____6038 = encode_formula lhs env in
                      (match uu____6038 with
                       | (l2,decls2) ->
                           let uu____6045 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6045, (FStar_List.append decls1 decls2)))))
        | uu____6047 -> failwith "impossible" in
      let mk_ite r uu___122_6062 =
        match uu___122_6062 with
        | (guard,uu____6066)::(_then,uu____6068)::(_else,uu____6070)::[] ->
            let uu____6099 = encode_formula guard env in
            (match uu____6099 with
             | (g,decls1) ->
                 let uu____6106 = encode_formula _then env in
                 (match uu____6106 with
                  | (t,decls2) ->
                      let uu____6113 = encode_formula _else env in
                      (match uu____6113 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6122 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6141 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6141 in
      let connectives =
        let uu____6153 =
          let uu____6162 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6162) in
        let uu____6175 =
          let uu____6185 =
            let uu____6194 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6194) in
          let uu____6207 =
            let uu____6217 =
              let uu____6227 =
                let uu____6236 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6236) in
              let uu____6249 =
                let uu____6259 =
                  let uu____6269 =
                    let uu____6278 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6278) in
                  [uu____6269;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6259 in
              uu____6227 :: uu____6249 in
            (FStar_Syntax_Const.imp_lid, mk_imp) :: uu____6217 in
          uu____6185 :: uu____6207 in
        uu____6153 :: uu____6175 in
      let rec fallback phi =
        match phi.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6440 = encode_formula phi' env in
            (match uu____6440 with
             | (phi,decls) ->
                 let uu____6447 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi, msg, r)) r in
                 (uu____6447, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6448 ->
            let uu____6453 = FStar_Syntax_Util.unmeta phi in
            encode_formula uu____6453 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6482 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6482 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6490;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6492;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6508 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6508 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head,args) ->
            let head = FStar_Syntax_Util.un_uinst head in
            (match ((head.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6540::(x,uu____6542)::(t,uu____6544)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6578 = encode_term x env in
                 (match uu____6578 with
                  | (x,decls) ->
                      let uu____6585 = encode_term t env in
                      (match uu____6585 with
                       | (t,decls') ->
                           let uu____6592 =
                             FStar_SMTEncoding_Term.mk_HasType x t in
                           (uu____6592, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6596)::(msg,uu____6598)::(phi,uu____6600)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6634 =
                   let uu____6637 =
                     let uu____6638 = FStar_Syntax_Subst.compress r in
                     uu____6638.FStar_Syntax_Syntax.n in
                   let uu____6641 =
                     let uu____6642 = FStar_Syntax_Subst.compress msg in
                     uu____6642.FStar_Syntax_Syntax.n in
                   (uu____6637, uu____6641) in
                 (match uu____6634 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6649))) ->
                      let phi =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r,
                                     false))))) None r in
                      fallback phi
                  | uu____6665 -> fallback phi)
             | uu____6668 when head_redex env head ->
                 let uu____6676 = whnf env phi in
                 encode_formula uu____6676 env
             | uu____6677 ->
                 let uu____6685 = encode_term phi env in
                 (match uu____6685 with
                  | (tt,decls) ->
                      let uu____6692 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___148_6693 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___148_6693.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___148_6693.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6692, decls)))
        | uu____6696 ->
            let uu____6697 = encode_term phi env in
            (match uu____6697 with
             | (tt,decls) ->
                 let uu____6704 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___149_6705 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___149_6705.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___149_6705.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6704, decls)) in
      let encode_q_body env bs ps body =
        let uu____6732 = encode_binders None bs env in
        match uu____6732 with
        | (vars,guards,env,decls,uu____6754) ->
            let uu____6761 =
              let uu____6768 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____6791 =
                          let uu____6796 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____6810  ->
                                    match uu____6810 with
                                    | (t,uu____6816) ->
                                        encode_term t
                                          (let uu___150_6817 = env in
                                           {
                                             bindings =
                                               (uu___150_6817.bindings);
                                             depth = (uu___150_6817.depth);
                                             tcenv = (uu___150_6817.tcenv);
                                             warn = (uu___150_6817.warn);
                                             cache = (uu___150_6817.cache);
                                             nolabels =
                                               (uu___150_6817.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___150_6817.encode_non_total_function_typ)
                                           }))) in
                          FStar_All.pipe_right uu____6796 FStar_List.unzip in
                        match uu____6791 with
                        | (p,decls) -> (p, (FStar_List.flatten decls)))) in
              FStar_All.pipe_right uu____6768 FStar_List.unzip in
            (match uu____6761 with
             | (pats,decls') ->
                 let uu____6869 = encode_formula body env in
                 (match uu____6869 with
                  | (body,decls'') ->
                      let guards =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____6888;
                             FStar_SMTEncoding_Term.rng = uu____6889;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____6897 -> guards in
                      let uu____6900 = FStar_SMTEncoding_Util.mk_and_l guards in
                      (vars, pats, uu____6900, body,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug phi;
      (let phi = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____6934  ->
                   match uu____6934 with
                   | (x,uu____6938) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats with
         | [] -> ()
         | hd::tl ->
             let pat_vars =
               let uu____6944 = FStar_Syntax_Free.names hd in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____6950 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____6950) uu____6944 tl in
             let uu____6952 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____6964  ->
                       match uu____6964 with
                       | (b,uu____6968) ->
                           let uu____6969 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____6969)) in
             (match uu____6952 with
              | None  -> ()
              | Some (x,uu____6973) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd.FStar_Syntax_Syntax.pos tl in
                  let uu____6983 =
                    let uu____6984 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____6984 in
                  FStar_Errors.warn pos uu____6983) in
       let uu____6985 = FStar_Syntax_Util.destruct_typ_as_formula phi in
       match uu____6985 with
       | None  -> fallback phi
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____6991 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7027  ->
                     match uu____7027 with
                     | (l,uu____7037) -> FStar_Ident.lid_equals op l)) in
           (match uu____6991 with
            | None  -> fallback phi
            | Some (uu____7060,f) -> f phi.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7089 = encode_q_body env vars pats body in
             match uu____7089 with
             | (vars,pats,guard,body,decls) ->
                 let tm =
                   let uu____7115 =
                     let uu____7121 =
                       FStar_SMTEncoding_Util.mkImp (guard, body) in
                     (pats, vars, uu____7121) in
                   FStar_SMTEncoding_Term.mkForall uu____7115
                     phi.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7133 = encode_q_body env vars pats body in
             match uu____7133 with
             | (vars,pats,guard,body,decls) ->
                 let uu____7158 =
                   let uu____7159 =
                     let uu____7165 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body) in
                     (pats, vars, uu____7165) in
                   FStar_SMTEncoding_Term.mkExists uu____7159
                     phi.FStar_Syntax_Syntax.pos in
                 (uu____7158, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7214 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7214 with
  | (asym,a) ->
      let uu____7219 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7219 with
       | (xsym,x) ->
           let uu____7224 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7224 with
            | (ysym,y) ->
                let quant vars body x =
                  let xname_decl =
                    let uu____7254 =
                      let uu____7260 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x, uu____7260, FStar_SMTEncoding_Term.Term_sort, None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7254 in
                  let xtok = Prims.strcat x "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7275 =
                      let uu____7279 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x, uu____7279) in
                    FStar_SMTEncoding_Util.mkApp uu____7275 in
                  let xtok = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok vars in
                  let uu____7287 =
                    let uu____7289 =
                      let uu____7291 =
                        let uu____7293 =
                          let uu____7294 =
                            let uu____7299 =
                              let uu____7300 =
                                let uu____7306 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7306) in
                              FStar_SMTEncoding_Util.mkForall uu____7300 in
                            (uu____7299, None,
                              (Some (Prims.strcat "primitive_" x))) in
                          FStar_SMTEncoding_Term.Assume uu____7294 in
                        let uu____7316 =
                          let uu____7318 =
                            let uu____7319 =
                              let uu____7324 =
                                let uu____7325 =
                                  let uu____7331 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7331) in
                                FStar_SMTEncoding_Util.mkForall uu____7325 in
                              (uu____7324,
                                (Some "Name-token correspondence"),
                                (Some
                                   (Prims.strcat "token_correspondence_" x))) in
                            FStar_SMTEncoding_Term.Assume uu____7319 in
                          [uu____7318] in
                        uu____7293 :: uu____7316 in
                      xtok_decl :: uu____7291 in
                    xname_decl :: uu____7289 in
                  (xtok, uu____7287) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims =
                  let uu____7381 =
                    let uu____7389 =
                      let uu____7395 =
                        let uu____7396 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7396 in
                      quant axy uu____7395 in
                    (FStar_Syntax_Const.op_Eq, uu____7389) in
                  let uu____7402 =
                    let uu____7411 =
                      let uu____7419 =
                        let uu____7425 =
                          let uu____7426 =
                            let uu____7427 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7427 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7426 in
                        quant axy uu____7425 in
                      (FStar_Syntax_Const.op_notEq, uu____7419) in
                    let uu____7433 =
                      let uu____7442 =
                        let uu____7450 =
                          let uu____7456 =
                            let uu____7457 =
                              let uu____7458 =
                                let uu____7461 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7462 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7461, uu____7462) in
                              FStar_SMTEncoding_Util.mkLT uu____7458 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7457 in
                          quant xy uu____7456 in
                        (FStar_Syntax_Const.op_LT, uu____7450) in
                      let uu____7468 =
                        let uu____7477 =
                          let uu____7485 =
                            let uu____7491 =
                              let uu____7492 =
                                let uu____7493 =
                                  let uu____7496 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7497 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7496, uu____7497) in
                                FStar_SMTEncoding_Util.mkLTE uu____7493 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7492 in
                            quant xy uu____7491 in
                          (FStar_Syntax_Const.op_LTE, uu____7485) in
                        let uu____7503 =
                          let uu____7512 =
                            let uu____7520 =
                              let uu____7526 =
                                let uu____7527 =
                                  let uu____7528 =
                                    let uu____7531 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7532 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7531, uu____7532) in
                                  FStar_SMTEncoding_Util.mkGT uu____7528 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7527 in
                              quant xy uu____7526 in
                            (FStar_Syntax_Const.op_GT, uu____7520) in
                          let uu____7538 =
                            let uu____7547 =
                              let uu____7555 =
                                let uu____7561 =
                                  let uu____7562 =
                                    let uu____7563 =
                                      let uu____7566 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7567 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7566, uu____7567) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7563 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7562 in
                                quant xy uu____7561 in
                              (FStar_Syntax_Const.op_GTE, uu____7555) in
                            let uu____7573 =
                              let uu____7582 =
                                let uu____7590 =
                                  let uu____7596 =
                                    let uu____7597 =
                                      let uu____7598 =
                                        let uu____7601 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7602 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7601, uu____7602) in
                                      FStar_SMTEncoding_Util.mkSub uu____7598 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7597 in
                                  quant xy uu____7596 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7590) in
                              let uu____7608 =
                                let uu____7617 =
                                  let uu____7625 =
                                    let uu____7631 =
                                      let uu____7632 =
                                        let uu____7633 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7633 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7632 in
                                    quant qx uu____7631 in
                                  (FStar_Syntax_Const.op_Minus, uu____7625) in
                                let uu____7639 =
                                  let uu____7648 =
                                    let uu____7656 =
                                      let uu____7662 =
                                        let uu____7663 =
                                          let uu____7664 =
                                            let uu____7667 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7668 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7667, uu____7668) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7664 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7663 in
                                      quant xy uu____7662 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7656) in
                                  let uu____7674 =
                                    let uu____7683 =
                                      let uu____7691 =
                                        let uu____7697 =
                                          let uu____7698 =
                                            let uu____7699 =
                                              let uu____7702 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7703 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7702, uu____7703) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7699 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7698 in
                                        quant xy uu____7697 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7691) in
                                    let uu____7709 =
                                      let uu____7718 =
                                        let uu____7726 =
                                          let uu____7732 =
                                            let uu____7733 =
                                              let uu____7734 =
                                                let uu____7737 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7738 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7737, uu____7738) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7734 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7733 in
                                          quant xy uu____7732 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7726) in
                                      let uu____7744 =
                                        let uu____7753 =
                                          let uu____7761 =
                                            let uu____7767 =
                                              let uu____7768 =
                                                let uu____7769 =
                                                  let uu____7772 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____7773 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____7772, uu____7773) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____7769 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____7768 in
                                            quant xy uu____7767 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____7761) in
                                        let uu____7779 =
                                          let uu____7788 =
                                            let uu____7796 =
                                              let uu____7802 =
                                                let uu____7803 =
                                                  let uu____7804 =
                                                    let uu____7807 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____7808 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____7807, uu____7808) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____7804 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____7803 in
                                              quant xy uu____7802 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____7796) in
                                          let uu____7814 =
                                            let uu____7823 =
                                              let uu____7831 =
                                                let uu____7837 =
                                                  let uu____7838 =
                                                    let uu____7839 =
                                                      let uu____7842 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____7843 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____7842,
                                                        uu____7843) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____7839 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____7838 in
                                                quant xy uu____7837 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____7831) in
                                            let uu____7849 =
                                              let uu____7858 =
                                                let uu____7866 =
                                                  let uu____7872 =
                                                    let uu____7873 =
                                                      let uu____7874 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____7874 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____7873 in
                                                  quant qx uu____7872 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____7866) in
                                              [uu____7858] in
                                            uu____7823 :: uu____7849 in
                                          uu____7788 :: uu____7814 in
                                        uu____7753 :: uu____7779 in
                                      uu____7718 :: uu____7744 in
                                    uu____7683 :: uu____7709 in
                                  uu____7648 :: uu____7674 in
                                uu____7617 :: uu____7639 in
                              uu____7582 :: uu____7608 in
                            uu____7547 :: uu____7573 in
                          uu____7512 :: uu____7538 in
                        uu____7477 :: uu____7503 in
                      uu____7442 :: uu____7468 in
                    uu____7411 :: uu____7433 in
                  uu____7381 :: uu____7402 in
                let mk l v =
                  let uu____8002 =
                    let uu____8007 =
                      FStar_All.pipe_right prims
                        (FStar_List.find
                           (fun uu____8039  ->
                              match uu____8039 with
                              | (l',uu____8048) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8007
                      (FStar_Option.map
                         (fun uu____8081  ->
                            match uu____8081 with | (uu____8092,b) -> b v)) in
                  FStar_All.pipe_right uu____8002 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims
                    (FStar_Util.for_some
                       (fun uu____8133  ->
                          match uu____8133 with
                          | (l',uu____8142) -> FStar_Ident.lid_equals l l')) in
                { mk; is }))
let pretype_axiom:
  FStar_SMTEncoding_Term.term ->
    (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.decl
  =
  fun tapp  ->
    fun vars  ->
      let uu____8165 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      match uu____8165 with
      | (xxsym,xx) ->
          let uu____8170 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
          (match uu____8170 with
           | (ffsym,ff) ->
               let xx_has_type =
                 FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
               let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
               let uu____8177 =
                 let uu____8182 =
                   let uu____8183 =
                     let uu____8189 =
                       let uu____8190 =
                         let uu____8193 =
                           let uu____8194 =
                             let uu____8197 =
                               FStar_SMTEncoding_Util.mkApp ("PreType", [xx]) in
                             (tapp, uu____8197) in
                           FStar_SMTEncoding_Util.mkEq uu____8194 in
                         (xx_has_type, uu____8193) in
                       FStar_SMTEncoding_Util.mkImp uu____8190 in
                     ([[xx_has_type]],
                       ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                       (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                       uu____8189) in
                   FStar_SMTEncoding_Util.mkForall uu____8183 in
                 let uu____8210 =
                   let uu____8212 =
                     let uu____8213 =
                       let uu____8214 = FStar_Util.digest_of_string tapp_hash in
                       Prims.strcat "pretyping_" uu____8214 in
                     varops.mk_unique uu____8213 in
                   Some uu____8212 in
                 (uu____8182, (Some "pretyping"), uu____8210) in
               FStar_SMTEncoding_Term.Assume uu____8177)
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
    let uu____8245 =
      let uu____8246 =
        let uu____8251 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8251, (Some "unit typing"), (Some "unit_typing")) in
      FStar_SMTEncoding_Term.Assume uu____8246 in
    let uu____8254 =
      let uu____8256 =
        let uu____8257 =
          let uu____8262 =
            let uu____8263 =
              let uu____8269 =
                let uu____8270 =
                  let uu____8273 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8273) in
                FStar_SMTEncoding_Util.mkImp uu____8270 in
              ([[typing_pred]], [xx], uu____8269) in
            mkForall_fuel uu____8263 in
          (uu____8262, (Some "unit inversion"), (Some "unit_inversion")) in
        FStar_SMTEncoding_Term.Assume uu____8257 in
      [uu____8256] in
    uu____8245 :: uu____8254 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8302 =
      let uu____8303 =
        let uu____8308 =
          let uu____8309 =
            let uu____8315 =
              let uu____8318 =
                let uu____8320 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8320] in
              [uu____8318] in
            let uu____8323 =
              let uu____8324 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8324 tt in
            (uu____8315, [bb], uu____8323) in
          FStar_SMTEncoding_Util.mkForall uu____8309 in
        (uu____8308, (Some "bool typing"), (Some "bool_typing")) in
      FStar_SMTEncoding_Term.Assume uu____8303 in
    let uu____8336 =
      let uu____8338 =
        let uu____8339 =
          let uu____8344 =
            let uu____8345 =
              let uu____8351 =
                let uu____8352 =
                  let uu____8355 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8355) in
                FStar_SMTEncoding_Util.mkImp uu____8352 in
              ([[typing_pred]], [xx], uu____8351) in
            mkForall_fuel uu____8345 in
          (uu____8344, (Some "bool inversion"), (Some "bool_inversion")) in
        FStar_SMTEncoding_Term.Assume uu____8339 in
      [uu____8338] in
    uu____8302 :: uu____8336 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8390 =
        let uu____8391 =
          let uu____8395 =
            let uu____8397 =
              let uu____8399 =
                let uu____8401 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8402 =
                  let uu____8404 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8404] in
                uu____8401 :: uu____8402 in
              tt :: uu____8399 in
            tt :: uu____8397 in
          ("Prims.Precedes", uu____8395) in
        FStar_SMTEncoding_Util.mkApp uu____8391 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8390 in
    let precedes_y_x =
      let uu____8407 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8407 in
    let uu____8409 =
      let uu____8410 =
        let uu____8415 =
          let uu____8416 =
            let uu____8422 =
              let uu____8425 =
                let uu____8427 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8427] in
              [uu____8425] in
            let uu____8430 =
              let uu____8431 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8431 tt in
            (uu____8422, [bb], uu____8430) in
          FStar_SMTEncoding_Util.mkForall uu____8416 in
        (uu____8415, (Some "int typing"), (Some "int_typing")) in
      FStar_SMTEncoding_Term.Assume uu____8410 in
    let uu____8443 =
      let uu____8445 =
        let uu____8446 =
          let uu____8451 =
            let uu____8452 =
              let uu____8458 =
                let uu____8459 =
                  let uu____8462 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8462) in
                FStar_SMTEncoding_Util.mkImp uu____8459 in
              ([[typing_pred]], [xx], uu____8458) in
            mkForall_fuel uu____8452 in
          (uu____8451, (Some "int inversion"), (Some "int_inversion")) in
        FStar_SMTEncoding_Term.Assume uu____8446 in
      let uu____8476 =
        let uu____8478 =
          let uu____8479 =
            let uu____8484 =
              let uu____8485 =
                let uu____8491 =
                  let uu____8492 =
                    let uu____8495 =
                      let uu____8496 =
                        let uu____8498 =
                          let uu____8500 =
                            let uu____8502 =
                              let uu____8503 =
                                let uu____8506 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8507 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8506, uu____8507) in
                              FStar_SMTEncoding_Util.mkGT uu____8503 in
                            let uu____8508 =
                              let uu____8510 =
                                let uu____8511 =
                                  let uu____8514 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8515 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8514, uu____8515) in
                                FStar_SMTEncoding_Util.mkGTE uu____8511 in
                              let uu____8516 =
                                let uu____8518 =
                                  let uu____8519 =
                                    let uu____8522 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8523 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8522, uu____8523) in
                                  FStar_SMTEncoding_Util.mkLT uu____8519 in
                                [uu____8518] in
                              uu____8510 :: uu____8516 in
                            uu____8502 :: uu____8508 in
                          typing_pred_y :: uu____8500 in
                        typing_pred :: uu____8498 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8496 in
                    (uu____8495, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8492 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8491) in
              mkForall_fuel uu____8485 in
            (uu____8484, (Some "well-founded ordering on nat (alt)"),
              (Some "well-founded-ordering-on-nat")) in
          FStar_SMTEncoding_Term.Assume uu____8479 in
        [uu____8478] in
      uu____8445 :: uu____8476 in
    uu____8409 :: uu____8443 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8554 =
      let uu____8555 =
        let uu____8560 =
          let uu____8561 =
            let uu____8567 =
              let uu____8570 =
                let uu____8572 = FStar_SMTEncoding_Term.boxString b in
                [uu____8572] in
              [uu____8570] in
            let uu____8575 =
              let uu____8576 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8576 tt in
            (uu____8567, [bb], uu____8575) in
          FStar_SMTEncoding_Util.mkForall uu____8561 in
        (uu____8560, (Some "string typing"), (Some "string_typing")) in
      FStar_SMTEncoding_Term.Assume uu____8555 in
    let uu____8588 =
      let uu____8590 =
        let uu____8591 =
          let uu____8596 =
            let uu____8597 =
              let uu____8603 =
                let uu____8604 =
                  let uu____8607 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8607) in
                FStar_SMTEncoding_Util.mkImp uu____8604 in
              ([[typing_pred]], [xx], uu____8603) in
            mkForall_fuel uu____8597 in
          (uu____8596, (Some "string inversion"), (Some "string_inversion")) in
        FStar_SMTEncoding_Term.Assume uu____8591 in
      [uu____8590] in
    uu____8554 :: uu____8588 in
  let mk_ref env reft_name uu____8630 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8641 =
        let uu____8645 =
          let uu____8647 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8647] in
        (reft_name, uu____8645) in
      FStar_SMTEncoding_Util.mkApp uu____8641 in
    let refb =
      let uu____8650 =
        let uu____8654 =
          let uu____8656 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8656] in
        (reft_name, uu____8654) in
      FStar_SMTEncoding_Util.mkApp uu____8650 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8660 =
      let uu____8661 =
        let uu____8666 =
          let uu____8667 =
            let uu____8673 =
              let uu____8674 =
                let uu____8677 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8677) in
              FStar_SMTEncoding_Util.mkImp uu____8674 in
            ([[typing_pred]], [xx; aa], uu____8673) in
          mkForall_fuel uu____8667 in
        (uu____8666, (Some "ref inversion"), (Some "ref_inversion")) in
      FStar_SMTEncoding_Term.Assume uu____8661 in
    let uu____8693 =
      let uu____8695 =
        let uu____8696 =
          let uu____8701 =
            let uu____8702 =
              let uu____8708 =
                let uu____8709 =
                  let uu____8712 =
                    FStar_SMTEncoding_Util.mkAnd (typing_pred, typing_pred_b) in
                  let uu____8713 =
                    let uu____8714 =
                      let uu____8717 = FStar_SMTEncoding_Util.mkFreeV aa in
                      let uu____8718 = FStar_SMTEncoding_Util.mkFreeV bb in
                      (uu____8717, uu____8718) in
                    FStar_SMTEncoding_Util.mkEq uu____8714 in
                  (uu____8712, uu____8713) in
                FStar_SMTEncoding_Util.mkImp uu____8709 in
              ([[typing_pred; typing_pred_b]], [xx; aa; bb], uu____8708) in
            mkForall_fuel' (Prims.parse_int "2") uu____8702 in
          (uu____8701, (Some "ref typing is injective"),
            (Some "ref_injectivity")) in
        FStar_SMTEncoding_Term.Assume uu____8696 in
      [uu____8695] in
    uu____8660 :: uu____8693 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), (Some "true_interp"))] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8762 =
      let uu____8763 =
        let uu____8768 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8768, (Some "False interpretation"), (Some "false_interp")) in
      FStar_SMTEncoding_Term.Assume uu____8763 in
    [uu____8762] in
  let mk_and_interp env conj uu____8780 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____8790 =
        let uu____8794 =
          let uu____8796 = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
          [uu____8796] in
        ("Valid", uu____8794) in
      FStar_SMTEncoding_Util.mkApp uu____8790 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8803 =
      let uu____8804 =
        let uu____8809 =
          let uu____8810 =
            let uu____8816 =
              let uu____8817 =
                let uu____8820 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____8820, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8817 in
            ([[valid]], [aa; bb], uu____8816) in
          FStar_SMTEncoding_Util.mkForall uu____8810 in
        (uu____8809, (Some "/\\ interpretation"), (Some "l_and-interp")) in
      FStar_SMTEncoding_Term.Assume uu____8804 in
    [uu____8803] in
  let mk_or_interp env disj uu____8845 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____8855 =
        let uu____8859 =
          let uu____8861 = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
          [uu____8861] in
        ("Valid", uu____8859) in
      FStar_SMTEncoding_Util.mkApp uu____8855 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8868 =
      let uu____8869 =
        let uu____8874 =
          let uu____8875 =
            let uu____8881 =
              let uu____8882 =
                let uu____8885 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____8885, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8882 in
            ([[valid]], [aa; bb], uu____8881) in
          FStar_SMTEncoding_Util.mkForall uu____8875 in
        (uu____8874, (Some "\\/ interpretation"), (Some "l_or-interp")) in
      FStar_SMTEncoding_Term.Assume uu____8869 in
    [uu____8868] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x = FStar_SMTEncoding_Util.mkFreeV xx in
    let y = FStar_SMTEncoding_Util.mkFreeV yy in
    let valid =
      let uu____8924 =
        let uu____8928 =
          let uu____8930 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x; y]) in
          [uu____8930] in
        ("Valid", uu____8928) in
      FStar_SMTEncoding_Util.mkApp uu____8924 in
    let uu____8933 =
      let uu____8934 =
        let uu____8939 =
          let uu____8940 =
            let uu____8946 =
              let uu____8947 =
                let uu____8950 = FStar_SMTEncoding_Util.mkEq (x, y) in
                (uu____8950, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8947 in
            ([[valid]], [aa; xx; yy], uu____8946) in
          FStar_SMTEncoding_Util.mkForall uu____8940 in
        (uu____8939, (Some "Eq2 interpretation"), (Some "eq2-interp")) in
      FStar_SMTEncoding_Term.Assume uu____8934 in
    [uu____8933] in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x = FStar_SMTEncoding_Util.mkFreeV xx in
    let y = FStar_SMTEncoding_Util.mkFreeV yy in
    let valid =
      let uu____8995 =
        let uu____8999 =
          let uu____9001 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x; y]) in
          [uu____9001] in
        ("Valid", uu____8999) in
      FStar_SMTEncoding_Util.mkApp uu____8995 in
    let uu____9004 =
      let uu____9005 =
        let uu____9010 =
          let uu____9011 =
            let uu____9017 =
              let uu____9018 =
                let uu____9021 = FStar_SMTEncoding_Util.mkEq (x, y) in
                (uu____9021, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9018 in
            ([[valid]], [aa; bb; xx; yy], uu____9017) in
          FStar_SMTEncoding_Util.mkForall uu____9011 in
        (uu____9010, (Some "Eq3 interpretation"), (Some "eq3-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9005 in
    [uu____9004] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9060 =
        let uu____9064 =
          let uu____9066 = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
          [uu____9066] in
        ("Valid", uu____9064) in
      FStar_SMTEncoding_Util.mkApp uu____9060 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9073 =
      let uu____9074 =
        let uu____9079 =
          let uu____9080 =
            let uu____9086 =
              let uu____9087 =
                let uu____9090 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9090, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9087 in
            ([[valid]], [aa; bb], uu____9086) in
          FStar_SMTEncoding_Util.mkForall uu____9080 in
        (uu____9079, (Some "==> interpretation"), (Some "l_imp-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9074 in
    [uu____9073] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9125 =
        let uu____9129 =
          let uu____9131 = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
          [uu____9131] in
        ("Valid", uu____9129) in
      FStar_SMTEncoding_Util.mkApp uu____9125 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9138 =
      let uu____9139 =
        let uu____9144 =
          let uu____9145 =
            let uu____9151 =
              let uu____9152 =
                let uu____9155 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9155, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9152 in
            ([[valid]], [aa; bb], uu____9151) in
          FStar_SMTEncoding_Util.mkForall uu____9145 in
        (uu____9144, (Some "<==> interpretation"), (Some "l_iff-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9139 in
    [uu____9138] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let valid =
      let uu____9186 =
        let uu____9190 =
          let uu____9192 = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
          [uu____9192] in
        ("Valid", uu____9190) in
      FStar_SMTEncoding_Util.mkApp uu____9186 in
    let not_valid_a =
      let uu____9196 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9196 in
    let uu____9198 =
      let uu____9199 =
        let uu____9204 =
          let uu____9205 =
            let uu____9211 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[valid]], [aa], uu____9211) in
          FStar_SMTEncoding_Util.mkForall uu____9205 in
        (uu____9204, (Some "not interpretation"), (Some "l_not-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9199 in
    [uu____9198] in
  let mk_forall_interp env for_all tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x = FStar_SMTEncoding_Util.mkFreeV xx in
    let valid =
      let uu____9248 =
        let uu____9252 =
          let uu____9254 = FStar_SMTEncoding_Util.mkApp (for_all, [a; b]) in
          [uu____9254] in
        ("Valid", uu____9252) in
      FStar_SMTEncoding_Util.mkApp uu____9248 in
    let valid_b_x =
      let uu____9258 =
        let uu____9262 =
          let uu____9264 = FStar_SMTEncoding_Util.mk_ApplyTT b x in
          [uu____9264] in
        ("Valid", uu____9262) in
      FStar_SMTEncoding_Util.mkApp uu____9258 in
    let uu____9266 =
      let uu____9267 =
        let uu____9272 =
          let uu____9273 =
            let uu____9279 =
              let uu____9280 =
                let uu____9283 =
                  let uu____9284 =
                    let uu____9290 =
                      let uu____9293 =
                        let uu____9295 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x a in
                        [uu____9295] in
                      [uu____9293] in
                    let uu____9298 =
                      let uu____9299 =
                        let uu____9302 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x a in
                        (uu____9302, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9299 in
                    (uu____9290, [xx], uu____9298) in
                  FStar_SMTEncoding_Util.mkForall uu____9284 in
                (uu____9283, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9280 in
            ([[valid]], [aa; bb], uu____9279) in
          FStar_SMTEncoding_Util.mkForall uu____9273 in
        (uu____9272, (Some "forall interpretation"), (Some "forall-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9267 in
    [uu____9266] in
  let mk_exists_interp env for_some tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x = FStar_SMTEncoding_Util.mkFreeV xx in
    let valid =
      let uu____9350 =
        let uu____9354 =
          let uu____9356 = FStar_SMTEncoding_Util.mkApp (for_some, [a; b]) in
          [uu____9356] in
        ("Valid", uu____9354) in
      FStar_SMTEncoding_Util.mkApp uu____9350 in
    let valid_b_x =
      let uu____9360 =
        let uu____9364 =
          let uu____9366 = FStar_SMTEncoding_Util.mk_ApplyTT b x in
          [uu____9366] in
        ("Valid", uu____9364) in
      FStar_SMTEncoding_Util.mkApp uu____9360 in
    let uu____9368 =
      let uu____9369 =
        let uu____9374 =
          let uu____9375 =
            let uu____9381 =
              let uu____9382 =
                let uu____9385 =
                  let uu____9386 =
                    let uu____9392 =
                      let uu____9395 =
                        let uu____9397 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x a in
                        [uu____9397] in
                      [uu____9395] in
                    let uu____9400 =
                      let uu____9401 =
                        let uu____9404 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x a in
                        (uu____9404, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9401 in
                    (uu____9392, [xx], uu____9400) in
                  FStar_SMTEncoding_Util.mkExists uu____9386 in
                (uu____9385, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9382 in
            ([[valid]], [aa; bb], uu____9381) in
          FStar_SMTEncoding_Util.mkForall uu____9375 in
        (uu____9374, (Some "exists interpretation"), (Some "exists-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9369 in
    [uu____9368] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9441 =
      let uu____9442 =
        let uu____9447 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9448 =
          let uu____9450 = varops.mk_unique "typing_range_const" in
          Some uu____9450 in
        (uu____9447, (Some "Range_const typing"), uu____9448) in
      FStar_SMTEncoding_Term.Assume uu____9442 in
    [uu____9441] in
  let prims =
    [(FStar_Syntax_Const.unit_lid, mk_unit);
    (FStar_Syntax_Const.bool_lid, mk_bool);
    (FStar_Syntax_Const.int_lid, mk_int);
    (FStar_Syntax_Const.string_lid, mk_str);
    (FStar_Syntax_Const.ref_lid, mk_ref);
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
          let uu____9713 =
            FStar_Util.find_opt
              (fun uu____9731  ->
                 match uu____9731 with
                 | (l,uu____9741) -> FStar_Ident.lid_equals l t) prims in
          match uu____9713 with
          | None  -> []
          | Some (uu____9763,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9800 = encode_function_type_as_formula None None t env in
        match uu____9800 with
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
            let uu____9833 =
              (let uu____9834 =
                 FStar_Syntax_Util.is_pure_or_ghost_function t_norm in
               FStar_All.pipe_left Prims.op_Negation uu____9834) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            match uu____9833 with
            | true  ->
                let uu____9838 = new_term_constant_and_tok_from_lid env lid in
                (match uu____9838 with
                 | (vname,vtok,env) ->
                     let arg_sorts =
                       let uu____9850 =
                         let uu____9851 = FStar_Syntax_Subst.compress t_norm in
                         uu____9851.FStar_Syntax_Syntax.n in
                       match uu____9850 with
                       | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9856) ->
                           FStar_All.pipe_right binders
                             (FStar_List.map
                                (fun uu____9873  ->
                                   FStar_SMTEncoding_Term.Term_sort))
                       | uu____9876 -> [] in
                     let d =
                       FStar_SMTEncoding_Term.DeclFun
                         (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                           (Some
                              "Uninterpreted function symbol for impure function")) in
                     let dd =
                       FStar_SMTEncoding_Term.DeclFun
                         (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                           (Some "Uninterpreted name for impure function")) in
                     ([d; dd], env))
            | uu____9884 ->
                let uu____9885 = prims.is lid in
                (match uu____9885 with
                 | true  ->
                     let vname = varops.new_fvar lid in
                     let uu____9890 = prims.mk lid vname in
                     (match uu____9890 with
                      | (tok,definition) ->
                          let env = push_free_var env lid vname (Some tok) in
                          (definition, env))
                 | uu____9903 ->
                     let encode_non_total_function_typ =
                       lid.FStar_Ident.nsstr <> "Prims" in
                     let uu____9905 =
                       let uu____9911 = curried_arrow_formals_comp t_norm in
                       match uu____9911 with
                       | (args,comp) ->
                           (match encode_non_total_function_typ with
                            | true  ->
                                let uu____9926 =
                                  FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                    env.tcenv comp in
                                (args, uu____9926)
                            | uu____9933 ->
                                (args,
                                  (None,
                                    (FStar_Syntax_Util.comp_result comp)))) in
                     (match uu____9905 with
                      | (formals,(pre_opt,res_t)) ->
                          let uu____9953 =
                            new_term_constant_and_tok_from_lid env lid in
                          (match uu____9953 with
                           | (vname,vtok,env) ->
                               let vtok_tm =
                                 match formals with
                                 | [] ->
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (vname,
                                         FStar_SMTEncoding_Term.Term_sort)
                                 | uu____9966 ->
                                     FStar_SMTEncoding_Util.mkApp (vtok, []) in
                               let mk_disc_proj_axioms guard encoded_res_t
                                 vapp vars =
                                 FStar_All.pipe_right quals
                                   (FStar_List.collect
                                      (fun uu___123_9990  ->
                                         match uu___123_9990 with
                                         | FStar_Syntax_Syntax.Discriminator
                                             d ->
                                             let uu____9993 =
                                               FStar_Util.prefix vars in
                                             (match uu____9993 with
                                              | (uu____10004,(xxsym,uu____10006))
                                                  ->
                                                  let xx =
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                      (xxsym,
                                                        FStar_SMTEncoding_Term.Term_sort) in
                                                  let uu____10016 =
                                                    let uu____10017 =
                                                      let uu____10022 =
                                                        let uu____10023 =
                                                          let uu____10029 =
                                                            let uu____10030 =
                                                              let uu____10033
                                                                =
                                                                let uu____10034
                                                                  =
                                                                  FStar_SMTEncoding_Term.mk_tester
                                                                    (
                                                                    escape
                                                                    d.FStar_Ident.str)
                                                                    xx in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                  uu____10034 in
                                                              (vapp,
                                                                uu____10033) in
                                                            FStar_SMTEncoding_Util.mkEq
                                                              uu____10030 in
                                                          ([[vapp]], vars,
                                                            uu____10029) in
                                                        FStar_SMTEncoding_Util.mkForall
                                                          uu____10023 in
                                                      (uu____10022,
                                                        (Some
                                                           "Discriminator equation"),
                                                        (Some
                                                           (Prims.strcat
                                                              "disc_equation_"
                                                              (escape
                                                                 d.FStar_Ident.str)))) in
                                                    FStar_SMTEncoding_Term.Assume
                                                      uu____10017 in
                                                  [uu____10016])
                                         | FStar_Syntax_Syntax.Projector
                                             (d,f) ->
                                             let uu____10046 =
                                               FStar_Util.prefix vars in
                                             (match uu____10046 with
                                              | (uu____10057,(xxsym,uu____10059))
                                                  ->
                                                  let xx =
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                      (xxsym,
                                                        FStar_SMTEncoding_Term.Term_sort) in
                                                  let f =
                                                    {
                                                      FStar_Syntax_Syntax.ppname
                                                        = f;
                                                      FStar_Syntax_Syntax.index
                                                        =
                                                        (Prims.parse_int "0");
                                                      FStar_Syntax_Syntax.sort
                                                        =
                                                        FStar_Syntax_Syntax.tun
                                                    } in
                                                  let tp_name =
                                                    mk_term_projector_name d
                                                      f in
                                                  let prim_app =
                                                    FStar_SMTEncoding_Util.mkApp
                                                      (tp_name, [xx]) in
                                                  let uu____10073 =
                                                    let uu____10074 =
                                                      let uu____10079 =
                                                        let uu____10080 =
                                                          let uu____10086 =
                                                            FStar_SMTEncoding_Util.mkEq
                                                              (vapp,
                                                                prim_app) in
                                                          ([[vapp]], vars,
                                                            uu____10086) in
                                                        FStar_SMTEncoding_Util.mkForall
                                                          uu____10080 in
                                                      (uu____10079,
                                                        (Some
                                                           "Projector equation"),
                                                        (Some
                                                           (Prims.strcat
                                                              "proj_equation_"
                                                              tp_name))) in
                                                    FStar_SMTEncoding_Term.Assume
                                                      uu____10074 in
                                                  [uu____10073])
                                         | uu____10096 -> [])) in
                               let uu____10097 =
                                 encode_binders None formals env in
                               (match uu____10097 with
                                | (vars,guards,env',decls1,uu____10113) ->
                                    let uu____10120 =
                                      match pre_opt with
                                      | None  ->
                                          let uu____10125 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              guards in
                                          (uu____10125, decls1)
                                      | Some p ->
                                          let uu____10127 =
                                            encode_formula p env' in
                                          (match uu____10127 with
                                           | (g,ds) ->
                                               let uu____10134 =
                                                 FStar_SMTEncoding_Util.mk_and_l
                                                   (g :: guards) in
                                               (uu____10134,
                                                 (FStar_List.append decls1 ds))) in
                                    (match uu____10120 with
                                     | (guard,decls1) ->
                                         let vtok_app = mk_Apply vtok_tm vars in
                                         let vapp =
                                           let uu____10143 =
                                             let uu____10147 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 vars in
                                             (vname, uu____10147) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____10143 in
                                         let uu____10152 =
                                           let vname_decl =
                                             let uu____10157 =
                                               let uu____10163 =
                                                 FStar_All.pipe_right formals
                                                   (FStar_List.map
                                                      (fun uu____10168  ->
                                                         FStar_SMTEncoding_Term.Term_sort)) in
                                               (vname, uu____10163,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 None) in
                                             FStar_SMTEncoding_Term.DeclFun
                                               uu____10157 in
                                           let uu____10173 =
                                             let env =
                                               let uu___151_10177 = env in
                                               {
                                                 bindings =
                                                   (uu___151_10177.bindings);
                                                 depth =
                                                   (uu___151_10177.depth);
                                                 tcenv =
                                                   (uu___151_10177.tcenv);
                                                 warn = (uu___151_10177.warn);
                                                 cache =
                                                   (uu___151_10177.cache);
                                                 nolabels =
                                                   (uu___151_10177.nolabels);
                                                 use_zfuel_name =
                                                   (uu___151_10177.use_zfuel_name);
                                                 encode_non_total_function_typ
                                               } in
                                             let uu____10178 =
                                               let uu____10179 =
                                                 head_normal env tt in
                                               Prims.op_Negation uu____10179 in
                                             match uu____10178 with
                                             | true  ->
                                                 encode_term_pred None tt env
                                                   vtok_tm
                                             | uu____10182 ->
                                                 encode_term_pred None t_norm
                                                   env vtok_tm in
                                           match uu____10173 with
                                           | (tok_typing,decls2) ->
                                               let tok_typing =
                                                 FStar_SMTEncoding_Term.Assume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Some
                                                        (Prims.strcat
                                                           "function_token_typing_"
                                                           vname))) in
                                               let uu____10191 =
                                                 match formals with
                                                 | [] ->
                                                     let uu____10200 =
                                                       let uu____10201 =
                                                         let uu____10203 =
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                             (vname,
                                                               FStar_SMTEncoding_Term.Term_sort) in
                                                         FStar_All.pipe_left
                                                           (fun _0_34  ->
                                                              Some _0_34)
                                                           uu____10203 in
                                                       push_free_var env lid
                                                         vname uu____10201 in
                                                     ((FStar_List.append
                                                         decls2 [tok_typing]),
                                                       uu____10200)
                                                 | uu____10206 ->
                                                     let vtok_decl =
                                                       FStar_SMTEncoding_Term.DeclFun
                                                         (vtok, [],
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           None) in
                                                     let vtok_fresh =
                                                       let uu____10211 =
                                                         varops.next_id () in
                                                       FStar_SMTEncoding_Term.fresh_token
                                                         (vtok,
                                                           FStar_SMTEncoding_Term.Term_sort)
                                                         uu____10211 in
                                                     let name_tok_corr =
                                                       let uu____10213 =
                                                         let uu____10218 =
                                                           let uu____10219 =
                                                             let uu____10225
                                                               =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (vtok_app,
                                                                   vapp) in
                                                             ([[vtok_app];
                                                              [vapp]], vars,
                                                               uu____10225) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____10219 in
                                                         (uu____10218,
                                                           (Some
                                                              "Name-token correspondence"),
                                                           (Some
                                                              (Prims.strcat
                                                                 "token_correspondence_"
                                                                 vname))) in
                                                       FStar_SMTEncoding_Term.Assume
                                                         uu____10213 in
                                                     ((FStar_List.append
                                                         decls2
                                                         [vtok_decl;
                                                         vtok_fresh;
                                                         name_tok_corr;
                                                         tok_typing]), env) in
                                               (match uu____10191 with
                                                | (tok_decl,env) ->
                                                    ((vname_decl ::
                                                      tok_decl), env)) in
                                         (match uu____10152 with
                                          | (decls2,env) ->
                                              let uu____10250 =
                                                let res_t =
                                                  FStar_Syntax_Subst.compress
                                                    res_t in
                                                let uu____10255 =
                                                  encode_term res_t env' in
                                                match uu____10255 with
                                                | (encoded_res_t,decls) ->
                                                    let uu____10263 =
                                                      FStar_SMTEncoding_Term.mk_HasType
                                                        vapp encoded_res_t in
                                                    (encoded_res_t,
                                                      uu____10263, decls) in
                                              (match uu____10250 with
                                               | (encoded_res_t,ty_pred,decls3)
                                                   ->
                                                   let typingAx =
                                                     let uu____10271 =
                                                       let uu____10276 =
                                                         let uu____10277 =
                                                           let uu____10283 =
                                                             FStar_SMTEncoding_Util.mkImp
                                                               (guard,
                                                                 ty_pred) in
                                                           ([[vapp]], vars,
                                                             uu____10283) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____10277 in
                                                       (uu____10276,
                                                         (Some
                                                            "free var typing"),
                                                         (Some
                                                            (Prims.strcat
                                                               "typing_"
                                                               vname))) in
                                                     FStar_SMTEncoding_Term.Assume
                                                       uu____10271 in
                                                   let freshness =
                                                     let uu____10293 =
                                                       FStar_All.pipe_right
                                                         quals
                                                         (FStar_List.contains
                                                            FStar_Syntax_Syntax.New) in
                                                     match uu____10293 with
                                                     | true  ->
                                                         let uu____10296 =
                                                           let uu____10297 =
                                                             let uu____10303
                                                               =
                                                               FStar_All.pipe_right
                                                                 vars
                                                                 (FStar_List.map
                                                                    Prims.snd) in
                                                             let uu____10309
                                                               =
                                                               varops.next_id
                                                                 () in
                                                             (vname,
                                                               uu____10303,
                                                               FStar_SMTEncoding_Term.Term_sort,
                                                               uu____10309) in
                                                           FStar_SMTEncoding_Term.fresh_constructor
                                                             uu____10297 in
                                                         let uu____10311 =
                                                           let uu____10313 =
                                                             pretype_axiom
                                                               vapp vars in
                                                           [uu____10313] in
                                                         uu____10296 ::
                                                           uu____10311
                                                     | uu____10314 -> [] in
                                                   let g =
                                                     let uu____10317 =
                                                       let uu____10319 =
                                                         let uu____10321 =
                                                           let uu____10323 =
                                                             let uu____10325
                                                               =
                                                               mk_disc_proj_axioms
                                                                 guard
                                                                 encoded_res_t
                                                                 vapp vars in
                                                             typingAx ::
                                                               uu____10325 in
                                                           FStar_List.append
                                                             freshness
                                                             uu____10323 in
                                                         FStar_List.append
                                                           decls3 uu____10321 in
                                                       FStar_List.append
                                                         decls2 uu____10319 in
                                                     FStar_List.append decls1
                                                       uu____10317 in
                                                   (g, env))))))))
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
          let uu____10347 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10347 with
          | None  ->
              let uu____10370 = encode_free_var env x t t_norm [] in
              (match uu____10370 with
               | (decls,env) ->
                   let uu____10385 =
                     lookup_lid env
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10385 with
                    | (n,x',uu____10404) -> ((n, x'), decls, env)))
          | Some (n,x,uu____10416) -> ((n, x), [], env)
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
          let uu____10449 = encode_free_var env lid t tt quals in
          match uu____10449 with
          | (decls,env) ->
              let uu____10460 = FStar_Syntax_Util.is_smt_lemma t in
              (match uu____10460 with
               | true  ->
                   let uu____10464 =
                     let uu____10466 = encode_smt_lemma env lid tt in
                     FStar_List.append decls uu____10466 in
                   (uu____10464, env)
               | uu____10469 -> (decls, env))
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
             (fun uu____10494  ->
                fun lb  ->
                  match uu____10494 with
                  | (decls,env) ->
                      let uu____10506 =
                        let uu____10510 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env uu____10510
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10506 with
                       | (decls',env) ->
                           ((FStar_List.append decls decls'), env)))
             ([], env))
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10534  ->
      fun quals  ->
        match uu____10534 with
        | (is_rec,bindings) ->
            let eta_expand binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10583 = FStar_Util.first_N nbinders formals in
              match uu____10583 with
              | (formals,extra_formals) ->
                  let subst =
                    FStar_List.map2
                      (fun uu____10623  ->
                         fun uu____10624  ->
                           match (uu____10623, uu____10624) with
                           | ((formal,uu____10634),(binder,uu____10636)) ->
                               let uu____10641 =
                                 let uu____10646 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10646) in
                               FStar_Syntax_Syntax.NT uu____10641) formals
                      binders in
                  let extra_formals =
                    let uu____10651 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10665  ->
                              match uu____10665 with
                              | (x,i) ->
                                  let uu____10672 =
                                    let uu___152_10673 = x in
                                    let uu____10674 =
                                      FStar_Syntax_Subst.subst subst
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___152_10673.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___152_10673.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10674
                                    } in
                                  (uu____10672, i))) in
                    FStar_All.pipe_right uu____10651
                      FStar_Syntax_Util.name_binders in
                  let body =
                    let uu____10686 =
                      let uu____10688 =
                        let uu____10689 = FStar_Syntax_Subst.subst subst t in
                        uu____10689.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10688 in
                    let uu____10693 =
                      let uu____10694 = FStar_Syntax_Subst.compress body in
                      let uu____10695 =
                        let uu____10696 =
                          FStar_Syntax_Util.args_of_binders extra_formals in
                        FStar_All.pipe_left Prims.snd uu____10696 in
                      FStar_Syntax_Syntax.extend_app_n uu____10694
                        uu____10695 in
                    uu____10693 uu____10686 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals), body) in
            let destruct_bound_function flid t_norm e =
              let rec aux norm t_norm =
                let uu____10755 = FStar_Syntax_Util.abs_formals e in
                match uu____10755 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____10808::uu____10809 ->
                         let uu____10817 =
                           let uu____10818 =
                             FStar_Syntax_Subst.compress t_norm in
                           uu____10818.FStar_Syntax_Syntax.n in
                         (match uu____10817 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____10847 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____10847 with
                               | (formals,c) ->
                                   let nformals = FStar_List.length formals in
                                   let nbinders = FStar_List.length binders in
                                   let tres = FStar_Syntax_Util.comp_result c in
                                   let uu____10877 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c) in
                                   (match uu____10877 with
                                    | true  ->
                                        let uu____10897 =
                                          FStar_Util.first_N nformals binders in
                                        (match uu____10897 with
                                         | (bs0,rest) ->
                                             let c =
                                               let subst =
                                                 FStar_List.map2
                                                   (fun uu____10945  ->
                                                      fun uu____10946  ->
                                                        match (uu____10945,
                                                                uu____10946)
                                                        with
                                                        | ((b,uu____10956),
                                                           (x,uu____10958))
                                                            ->
                                                            let uu____10963 =
                                                              let uu____10968
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  x in
                                                              (b,
                                                                uu____10968) in
                                                            FStar_Syntax_Syntax.NT
                                                              uu____10963)
                                                   bs0 formals in
                                               FStar_Syntax_Subst.subst_comp
                                                 subst c in
                                             let body =
                                               FStar_Syntax_Util.abs rest
                                                 body lopt in
                                             ((bs0, body, bs0,
                                                (FStar_Syntax_Util.comp_result
                                                   c)), false))
                                    | uu____10990 ->
                                        (match nformals > nbinders with
                                         | true  ->
                                             let uu____11010 =
                                               eta_expand binders formals
                                                 body tres in
                                             (match uu____11010 with
                                              | (binders,body) ->
                                                  ((binders, body, formals,
                                                     tres), false))
                                         | uu____11062 ->
                                             ((binders, body, formals, tres),
                                               false))))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11072) ->
                              let uu____11077 =
                                let uu____11090 =
                                  aux norm x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11090 in
                              (uu____11077, true)
                          | uu____11129 when Prims.op_Negation norm ->
                              let t_norm =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.Beta;
                                  FStar_TypeChecker_Normalize.WHNF;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant;
                                  FStar_TypeChecker_Normalize.EraseUniverses]
                                  env.tcenv t_norm in
                              aux true t_norm
                          | uu____11131 ->
                              let uu____11132 =
                                let uu____11133 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11134 =
                                  FStar_Syntax_Print.term_to_string t_norm in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11133
                                  uu____11134 in
                              failwith uu____11132)
                     | uu____11149 ->
                         let uu____11150 =
                           let uu____11151 =
                             FStar_Syntax_Subst.compress t_norm in
                           uu____11151.FStar_Syntax_Syntax.n in
                         (match uu____11150 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11180 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11180 with
                               | (formals,c) ->
                                   let tres = FStar_Syntax_Util.comp_result c in
                                   let uu____11202 =
                                     eta_expand [] formals e tres in
                                   (match uu____11202 with
                                    | (binders,body) ->
                                        ((binders, body, formals, tres),
                                          false)))
                          | uu____11256 -> (([], e, [], t_norm), false))) in
              aux false t_norm in
            (try
               let uu____11284 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         FStar_Syntax_Util.is_lemma
                           lb.FStar_Syntax_Syntax.lbtyp)) in
               match uu____11284 with
               | true  -> encode_top_level_vals env bindings quals
               | uu____11290 ->
                   let uu____11291 =
                     FStar_All.pipe_right bindings
                       (FStar_List.fold_left
                          (fun uu____11332  ->
                             fun lb  ->
                               match uu____11332 with
                               | (toks,typs,decls,env) ->
                                   ((let uu____11383 =
                                       FStar_Syntax_Util.is_lemma
                                         lb.FStar_Syntax_Syntax.lbtyp in
                                     match uu____11383 with
                                     | true  ->
                                         Prims.raise Let_rec_unencodeable
                                     | uu____11384 -> ());
                                    (let t_norm =
                                       whnf env lb.FStar_Syntax_Syntax.lbtyp in
                                     let uu____11386 =
                                       let uu____11394 =
                                         FStar_Util.right
                                           lb.FStar_Syntax_Syntax.lbname in
                                       declare_top_level_let env uu____11394
                                         lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                     match uu____11386 with
                                     | (tok,decl,env) ->
                                         let uu____11419 =
                                           let uu____11426 =
                                             let uu____11432 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             (uu____11432, tok) in
                                           uu____11426 :: toks in
                                         (uu____11419, (t_norm :: typs),
                                           (decl :: decls), env))))
                          ([], [], [], env)) in
                   (match uu____11291 with
                    | (toks,typs,decls,env) ->
                        let toks = FStar_List.rev toks in
                        let decls =
                          FStar_All.pipe_right (FStar_List.rev decls)
                            FStar_List.flatten in
                        let typs = FStar_List.rev typs in
                        let mk_app curry f ftok vars =
                          match vars with
                          | [] ->
                              FStar_SMTEncoding_Util.mkFreeV
                                (f, FStar_SMTEncoding_Term.Term_sort)
                          | uu____11534 ->
                              (match curry with
                               | true  ->
                                   (match ftok with
                                    | Some ftok -> mk_Apply ftok vars
                                    | None  ->
                                        let uu____11539 =
                                          FStar_SMTEncoding_Util.mkFreeV
                                            (f,
                                              FStar_SMTEncoding_Term.Term_sort) in
                                        mk_Apply uu____11539 vars)
                               | uu____11540 ->
                                   let uu____11541 =
                                     let uu____11545 =
                                       FStar_List.map
                                         FStar_SMTEncoding_Util.mkFreeV vars in
                                     (f, uu____11545) in
                                   FStar_SMTEncoding_Util.mkApp uu____11541) in
                        let uu____11550 =
                          (FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___124_11552  ->
                                   match uu___124_11552 with
                                   | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                       true
                                   | uu____11553 -> false)))
                            ||
                            (FStar_All.pipe_right typs
                               (FStar_Util.for_some
                                  (fun t  ->
                                     let uu____11556 =
                                       FStar_Syntax_Util.is_pure_or_ghost_function
                                         t in
                                     FStar_All.pipe_left Prims.op_Negation
                                       uu____11556))) in
                        (match uu____11550 with
                         | true  -> (decls, env)
                         | uu____11561 ->
                             (match Prims.op_Negation is_rec with
                              | true  ->
                                  (match (bindings, typs, toks) with
                                   | ({
                                        FStar_Syntax_Syntax.lbname =
                                          uu____11576;
                                        FStar_Syntax_Syntax.lbunivs =
                                          uu____11577;
                                        FStar_Syntax_Syntax.lbtyp =
                                          uu____11578;
                                        FStar_Syntax_Syntax.lbeff =
                                          uu____11579;
                                        FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                                      (flid_fv,(f,ftok))::[]) ->
                                       let e = FStar_Syntax_Subst.compress e in
                                       let flid =
                                         (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                       let uu____11621 =
                                         destruct_bound_function flid t_norm
                                           e in
                                       (match uu____11621 with
                                        | ((binders,body,uu____11633,uu____11634),curry)
                                            ->
                                            let uu____11640 =
                                              encode_binders None binders env in
                                            (match uu____11640 with
                                             | (vars,guards,env',binder_decls,uu____11656)
                                                 ->
                                                 let app =
                                                   mk_app curry f ftok vars in
                                                 let uu____11664 =
                                                   let uu____11669 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Logic) in
                                                   match uu____11669 with
                                                   | true  ->
                                                       let uu____11675 =
                                                         FStar_SMTEncoding_Term.mk_Valid
                                                           app in
                                                       let uu____11676 =
                                                         encode_formula body
                                                           env' in
                                                       (uu____11675,
                                                         uu____11676)
                                                   | uu____11681 ->
                                                       let uu____11682 =
                                                         encode_term body
                                                           env' in
                                                       (app, uu____11682) in
                                                 (match uu____11664 with
                                                  | (app,(body,decls2)) ->
                                                      let eqn =
                                                        let uu____11696 =
                                                          let uu____11701 =
                                                            let uu____11702 =
                                                              let uu____11708
                                                                =
                                                                FStar_SMTEncoding_Util.mkEq
                                                                  (app, body) in
                                                              ([[app]], vars,
                                                                uu____11708) in
                                                            FStar_SMTEncoding_Util.mkForall
                                                              uu____11702 in
                                                          let uu____11714 =
                                                            let uu____11716 =
                                                              FStar_Util.format1
                                                                "Equation for %s"
                                                                flid.FStar_Ident.str in
                                                            Some uu____11716 in
                                                          (uu____11701,
                                                            uu____11714,
                                                            (Some
                                                               (Prims.strcat
                                                                  "equation_"
                                                                  f))) in
                                                        FStar_SMTEncoding_Term.Assume
                                                          uu____11696 in
                                                      let uu____11719 =
                                                        let uu____11721 =
                                                          let uu____11723 =
                                                            let uu____11725 =
                                                              let uu____11727
                                                                =
                                                                primitive_type_axioms
                                                                  env.tcenv
                                                                  flid f app in
                                                              FStar_List.append
                                                                [eqn]
                                                                uu____11727 in
                                                            FStar_List.append
                                                              decls2
                                                              uu____11725 in
                                                          FStar_List.append
                                                            binder_decls
                                                            uu____11723 in
                                                        FStar_List.append
                                                          decls uu____11721 in
                                                      (uu____11719, env))))
                                   | uu____11730 -> failwith "Impossible")
                              | uu____11745 ->
                                  let fuel =
                                    let uu____11749 = varops.fresh "fuel" in
                                    (uu____11749,
                                      FStar_SMTEncoding_Term.Fuel_sort) in
                                  let fuel_tm =
                                    FStar_SMTEncoding_Util.mkFreeV fuel in
                                  let env0 = env in
                                  let uu____11752 =
                                    FStar_All.pipe_right toks
                                      (FStar_List.fold_left
                                         (fun uu____11791  ->
                                            fun uu____11792  ->
                                              match (uu____11791,
                                                      uu____11792)
                                              with
                                              | ((gtoks,env),(flid_fv,
                                                              (f,ftok)))
                                                  ->
                                                  let flid =
                                                    (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                                  let g =
                                                    let uu____11874 =
                                                      FStar_Ident.lid_add_suffix
                                                        flid
                                                        "fuel_instrumented" in
                                                    varops.new_fvar
                                                      uu____11874 in
                                                  let gtok =
                                                    let uu____11876 =
                                                      FStar_Ident.lid_add_suffix
                                                        flid
                                                        "fuel_instrumented_token" in
                                                    varops.new_fvar
                                                      uu____11876 in
                                                  let env =
                                                    let uu____11878 =
                                                      let uu____11880 =
                                                        FStar_SMTEncoding_Util.mkApp
                                                          (g, [fuel_tm]) in
                                                      FStar_All.pipe_left
                                                        (fun _0_36  ->
                                                           Some _0_36)
                                                        uu____11880 in
                                                    push_free_var env flid
                                                      gtok uu____11878 in
                                                  (((flid, f, ftok, g, gtok)
                                                    :: gtoks), env))
                                         ([], env)) in
                                  (match uu____11752 with
                                   | (gtoks,env) ->
                                       let gtoks = FStar_List.rev gtoks in
                                       let encode_one_binding env0
                                         uu____11964 t_norm uu____11966 =
                                         match (uu____11964, uu____11966)
                                         with
                                         | ((flid,f,ftok,g,gtok),{
                                                                   FStar_Syntax_Syntax.lbname
                                                                    = lbn;
                                                                   FStar_Syntax_Syntax.lbunivs
                                                                    =
                                                                    uu____11990;
                                                                   FStar_Syntax_Syntax.lbtyp
                                                                    =
                                                                    uu____11991;
                                                                   FStar_Syntax_Syntax.lbeff
                                                                    =
                                                                    uu____11992;
                                                                   FStar_Syntax_Syntax.lbdef
                                                                    = e;_})
                                             ->
                                             ((let uu____12010 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env0.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               match uu____12010 with
                                               | true  ->
                                                   let uu____12011 =
                                                     FStar_Syntax_Print.lbname_to_string
                                                       lbn in
                                                   let uu____12012 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t_norm in
                                                   let uu____12013 =
                                                     FStar_Syntax_Print.term_to_string
                                                       e in
                                                   FStar_Util.print3
                                                     "Encoding let rec %s : %s = %s\n"
                                                     uu____12011 uu____12012
                                                     uu____12013
                                               | uu____12014 -> ());
                                              (let uu____12015 =
                                                 destruct_bound_function flid
                                                   t_norm e in
                                               match uu____12015 with
                                               | ((binders,body,formals,tres),curry)
                                                   ->
                                                   ((let uu____12037 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env0.tcenv)
                                                         (FStar_Options.Other
                                                            "SMTEncoding") in
                                                     match uu____12037 with
                                                     | true  ->
                                                         let uu____12038 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", " binders in
                                                         let uu____12039 =
                                                           FStar_Syntax_Print.term_to_string
                                                             body in
                                                         FStar_Util.print2
                                                           "Encoding let rec: binders=[%s], body=%s\n"
                                                           uu____12038
                                                           uu____12039
                                                     | uu____12040 -> ());
                                                    (match curry with
                                                     | true  ->
                                                         failwith
                                                           "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                     | uu____12042 -> ());
                                                    (let uu____12043 =
                                                       encode_binders None
                                                         binders env in
                                                     match uu____12043 with
                                                     | (vars,guards,env',binder_decls,uu____12061)
                                                         ->
                                                         let decl_g =
                                                           let uu____12069 =
                                                             let uu____12075
                                                               =
                                                               let uu____12077
                                                                 =
                                                                 FStar_List.map
                                                                   Prims.snd
                                                                   vars in
                                                               FStar_SMTEncoding_Term.Fuel_sort
                                                                 ::
                                                                 uu____12077 in
                                                             (g, uu____12075,
                                                               FStar_SMTEncoding_Term.Term_sort,
                                                               (Some
                                                                  "Fuel-instrumented function name")) in
                                                           FStar_SMTEncoding_Term.DeclFun
                                                             uu____12069 in
                                                         let env0 =
                                                           push_zfuel_name
                                                             env0 flid g in
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
                                                           let uu____12092 =
                                                             let uu____12096
                                                               =
                                                               FStar_List.map
                                                                 FStar_SMTEncoding_Util.mkFreeV
                                                                 vars in
                                                             (f, uu____12096) in
                                                           FStar_SMTEncoding_Util.mkApp
                                                             uu____12092 in
                                                         let gsapp =
                                                           let uu____12102 =
                                                             let uu____12106
                                                               =
                                                               let uu____12108
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkApp
                                                                   ("SFuel",
                                                                    [fuel_tm]) in
                                                               uu____12108 ::
                                                                 vars_tm in
                                                             (g, uu____12106) in
                                                           FStar_SMTEncoding_Util.mkApp
                                                             uu____12102 in
                                                         let gmax =
                                                           let uu____12112 =
                                                             let uu____12116
                                                               =
                                                               let uu____12118
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkApp
                                                                   ("MaxFuel",
                                                                    []) in
                                                               uu____12118 ::
                                                                 vars_tm in
                                                             (g, uu____12116) in
                                                           FStar_SMTEncoding_Util.mkApp
                                                             uu____12112 in
                                                         let uu____12121 =
                                                           encode_term body
                                                             env' in
                                                         (match uu____12121
                                                          with
                                                          | (body_tm,decls2)
                                                              ->
                                                              let eqn_g =
                                                                let uu____12132
                                                                  =
                                                                  let uu____12137
                                                                    =
                                                                    let uu____12138
                                                                    =
                                                                    let uu____12146
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                    ([
                                                                    [gsapp]],
                                                                    (Some
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12146) in
                                                                    FStar_SMTEncoding_Util.mkForall'
                                                                    uu____12138 in
                                                                  let uu____12157
                                                                    =
                                                                    let uu____12159
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                    Some
                                                                    uu____12159 in
                                                                  (uu____12137,
                                                                    uu____12157,
                                                                    (
                                                                    Some
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))) in
                                                                FStar_SMTEncoding_Term.Assume
                                                                  uu____12132 in
                                                              let eqn_f =
                                                                let uu____12163
                                                                  =
                                                                  let uu____12168
                                                                    =
                                                                    let uu____12169
                                                                    =
                                                                    let uu____12175
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____12175) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12169 in
                                                                  (uu____12168,
                                                                    (
                                                                    Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (
                                                                    Some
                                                                    (Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g))) in
                                                                FStar_SMTEncoding_Term.Assume
                                                                  uu____12163 in
                                                              let eqn_g' =
                                                                let uu____12184
                                                                  =
                                                                  let uu____12189
                                                                    =
                                                                    let uu____12190
                                                                    =
                                                                    let uu____12196
                                                                    =
                                                                    let uu____12197
                                                                    =
                                                                    let uu____12200
                                                                    =
                                                                    let uu____12201
                                                                    =
                                                                    let uu____12205
                                                                    =
                                                                    let uu____12207
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12207
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12205) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12201 in
                                                                    (gsapp,
                                                                    uu____12200) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12197 in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12196) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12190 in
                                                                  (uu____12189,
                                                                    (
                                                                    Some
                                                                    "Fuel irrelevance"),
                                                                    (
                                                                    Some
                                                                    (Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g))) in
                                                                FStar_SMTEncoding_Term.Assume
                                                                  uu____12184 in
                                                              let uu____12220
                                                                =
                                                                let uu____12225
                                                                  =
                                                                  encode_binders
                                                                    None
                                                                    formals
                                                                    env0 in
                                                                match uu____12225
                                                                with
                                                                | (vars,v_guards,env,binder_decls,uu____12242)
                                                                    ->
                                                                    let vars_tm
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                    let gapp
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm)) in
                                                                    let tok_corr
                                                                    =
                                                                    let tok_app
                                                                    =
                                                                    let uu____12257
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12257
                                                                    (fuel ::
                                                                    vars) in
                                                                    let uu____12260
                                                                    =
                                                                    let uu____12265
                                                                    =
                                                                    let uu____12266
                                                                    =
                                                                    let uu____12272
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12272) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12266 in
                                                                    (uu____12265,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12260 in
                                                                    let uu____12284
                                                                    =
                                                                    let uu____12288
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env gapp in
                                                                    match uu____12288
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____12296
                                                                    =
                                                                    let uu____12298
                                                                    =
                                                                    let uu____12299
                                                                    =
                                                                    let uu____12304
                                                                    =
                                                                    let uu____12305
                                                                    =
                                                                    let uu____12311
                                                                    =
                                                                    let uu____12312
                                                                    =
                                                                    let uu____12315
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12315,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12312 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12311) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12305 in
                                                                    (uu____12304,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12299 in
                                                                    [uu____12298] in
                                                                    (d3,
                                                                    uu____12296) in
                                                                    (match uu____12284
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                              (match uu____12220
                                                               with
                                                               | (aux_decls,g_typing)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls
                                                                    (FStar_List.append
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
                                                                    env0))))))) in
                                       let uu____12351 =
                                         let uu____12358 =
                                           FStar_List.zip3 gtoks typs
                                             bindings in
                                         FStar_List.fold_left
                                           (fun uu____12390  ->
                                              fun uu____12391  ->
                                                match (uu____12390,
                                                        uu____12391)
                                                with
                                                | ((decls,eqns,env0),
                                                   (gtok,ty,lb)) ->
                                                    let uu____12467 =
                                                      encode_one_binding env0
                                                        gtok ty lb in
                                                    (match uu____12467 with
                                                     | (decls',eqns',env0) ->
                                                         ((decls' :: decls),
                                                           (FStar_List.append
                                                              eqns' eqns),
                                                           env0)))
                                           ([decls], [], env0) uu____12358 in
                                       (match uu____12351 with
                                        | (decls,eqns,env0) ->
                                            let uu____12507 =
                                              let uu____12512 =
                                                FStar_All.pipe_right decls
                                                  FStar_List.flatten in
                                              FStar_All.pipe_right
                                                uu____12512
                                                (FStar_List.partition
                                                   (fun uu___125_12522  ->
                                                      match uu___125_12522
                                                      with
                                                      | FStar_SMTEncoding_Term.DeclFun
                                                          uu____12523 -> true
                                                      | uu____12529 -> false)) in
                                            (match uu____12507 with
                                             | (prefix_decls,rest) ->
                                                 let eqns =
                                                   FStar_List.rev eqns in
                                                 ((FStar_List.append
                                                     prefix_decls
                                                     (FStar_List.append rest
                                                        eqns)), env0)))))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12547 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12547
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
      (let uu____12580 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       match uu____12580 with
       | true  ->
           let uu____12581 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
             uu____12581
       | uu____12582 -> ());
      (let nm =
         let uu____12584 = FStar_Syntax_Util.lid_of_sigelt se in
         match uu____12584 with | None  -> "" | Some l -> l.FStar_Ident.str in
       let uu____12587 = encode_sigelt' env se in
       match uu____12587 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12596 =
                  let uu____12598 =
                    let uu____12599 = FStar_Util.format1 "<Skipped %s/>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12599 in
                  [uu____12598] in
                (uu____12596, e)
            | uu____12601 ->
                let uu____12602 =
                  let uu____12604 =
                    let uu____12606 =
                      let uu____12607 =
                        FStar_Util.format1 "<Start encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12607 in
                    uu____12606 :: g in
                  let uu____12608 =
                    let uu____12610 =
                      let uu____12611 =
                        FStar_Util.format1 "</end encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12611 in
                    [uu____12610] in
                  FStar_List.append uu____12604 uu____12608 in
                (uu____12602, e)))
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12619 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect (ed,uu____12630) ->
          let uu____12631 =
            let uu____12632 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12632 Prims.op_Negation in
          (match uu____12631 with
           | true  -> ([], env)
           | uu____12637 ->
               let close_effect_params tm =
                 match ed.FStar_Syntax_Syntax.binders with
                 | [] -> tm
                 | uu____12652 ->
                     let uu____12653 =
                       let uu____12656 =
                         let uu____12657 =
                           let uu____12672 =
                             FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                               (FStar_Util.Inr
                                  (FStar_Syntax_Const.effect_Tot_lid,
                                    [FStar_Syntax_Syntax.TOTAL])) in
                           ((ed.FStar_Syntax_Syntax.binders), tm,
                             uu____12672) in
                         FStar_Syntax_Syntax.Tm_abs uu____12657 in
                       FStar_Syntax_Syntax.mk uu____12656 in
                     uu____12653 None tm.FStar_Syntax_Syntax.pos in
               let encode_action env a =
                 let uu____12725 =
                   new_term_constant_and_tok_from_lid env
                     a.FStar_Syntax_Syntax.action_name in
                 match uu____12725 with
                 | (aname,atok,env) ->
                     let uu____12735 =
                       FStar_Syntax_Util.arrow_formals_comp
                         a.FStar_Syntax_Syntax.action_typ in
                     (match uu____12735 with
                      | (formals,uu____12745) ->
                          let uu____12752 =
                            let uu____12755 =
                              close_effect_params
                                a.FStar_Syntax_Syntax.action_defn in
                            encode_term uu____12755 env in
                          (match uu____12752 with
                           | (tm,decls) ->
                               let a_decls =
                                 let uu____12763 =
                                   let uu____12764 =
                                     let uu____12770 =
                                       FStar_All.pipe_right formals
                                         (FStar_List.map
                                            (fun uu____12778  ->
                                               FStar_SMTEncoding_Term.Term_sort)) in
                                     (aname, uu____12770,
                                       FStar_SMTEncoding_Term.Term_sort,
                                       (Some "Action")) in
                                   FStar_SMTEncoding_Term.DeclFun uu____12764 in
                                 [uu____12763;
                                 FStar_SMTEncoding_Term.DeclFun
                                   (atok, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action token"))] in
                               let uu____12785 =
                                 let uu____12792 =
                                   FStar_All.pipe_right formals
                                     (FStar_List.map
                                        (fun uu____12812  ->
                                           match uu____12812 with
                                           | (bv,uu____12820) ->
                                               let uu____12821 =
                                                 gen_term_var env bv in
                                               (match uu____12821 with
                                                | (xxsym,xx,uu____12831) ->
                                                    ((xxsym,
                                                       FStar_SMTEncoding_Term.Term_sort),
                                                      xx)))) in
                                 FStar_All.pipe_right uu____12792
                                   FStar_List.split in
                               (match uu____12785 with
                                | (xs_sorts,xs) ->
                                    let app =
                                      let uu____12861 =
                                        let uu____12865 =
                                          let uu____12867 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (aname, xs) in
                                          [uu____12867] in
                                        ("Reify", uu____12865) in
                                      FStar_SMTEncoding_Util.mkApp
                                        uu____12861 in
                                    let a_eq =
                                      let uu____12871 =
                                        let uu____12876 =
                                          let uu____12877 =
                                            let uu____12883 =
                                              let uu____12884 =
                                                let uu____12887 =
                                                  mk_Apply tm xs_sorts in
                                                (app, uu____12887) in
                                              FStar_SMTEncoding_Util.mkEq
                                                uu____12884 in
                                            ([[app]], xs_sorts, uu____12883) in
                                          FStar_SMTEncoding_Util.mkForall
                                            uu____12877 in
                                        (uu____12876,
                                          (Some "Action equality"),
                                          (Some
                                             (Prims.strcat aname "_equality"))) in
                                      FStar_SMTEncoding_Term.Assume
                                        uu____12871 in
                                    let tok_correspondence =
                                      let tok_term =
                                        FStar_SMTEncoding_Util.mkFreeV
                                          (atok,
                                            FStar_SMTEncoding_Term.Term_sort) in
                                      let tok_app =
                                        mk_Apply tok_term xs_sorts in
                                      let uu____12900 =
                                        let uu____12905 =
                                          let uu____12906 =
                                            let uu____12912 =
                                              FStar_SMTEncoding_Util.mkEq
                                                (tok_app, app) in
                                            ([[tok_app]], xs_sorts,
                                              uu____12912) in
                                          FStar_SMTEncoding_Util.mkForall
                                            uu____12906 in
                                        (uu____12905,
                                          (Some "Action token correspondence"),
                                          (Some
                                             (Prims.strcat aname
                                                "_token_correspondence"))) in
                                      FStar_SMTEncoding_Term.Assume
                                        uu____12900 in
                                    (env,
                                      (FStar_List.append decls
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])))))) in
               let uu____12923 =
                 FStar_Util.fold_map encode_action env
                   ed.FStar_Syntax_Syntax.actions in
               (match uu____12923 with
                | (env,decls2) -> ((FStar_List.flatten decls2), env)))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____12939,uu____12940,uu____12941,uu____12942) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____12945 = new_term_constant_and_tok_from_lid env lid in
          (match uu____12945 with | (tname,ttok,env) -> ([], env))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____12956,t,quals,uu____12959) ->
          let will_encode_definition =
            let uu____12963 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___126_12965  ->
                      match uu___126_12965 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____12968 -> false)) in
            Prims.op_Negation uu____12963 in
          (match will_encode_definition with
           | true  -> ([], env)
           | uu____12972 ->
               let fv =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_constant None in
               let uu____12974 = encode_top_level_val env fv t quals in
               (match uu____12974 with
                | (decls,env) ->
                    let tname = lid.FStar_Ident.str in
                    let tsym =
                      FStar_SMTEncoding_Util.mkFreeV
                        (tname, FStar_SMTEncoding_Term.Term_sort) in
                    let uu____12986 =
                      let uu____12988 =
                        primitive_type_axioms env.tcenv lid tname tsym in
                      FStar_List.append decls uu____12988 in
                    (uu____12986, env)))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____12993,uu____12994) ->
          let uu____12997 = encode_formula f env in
          (match uu____12997 with
           | (f,decls) ->
               let g =
                 let uu____13006 =
                   let uu____13007 =
                     let uu____13012 =
                       let uu____13014 =
                         let uu____13015 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13015 in
                       Some uu____13014 in
                     let uu____13016 =
                       let uu____13018 =
                         varops.mk_unique
                           (Prims.strcat "assumption_" l.FStar_Ident.str) in
                       Some uu____13018 in
                     (f, uu____13012, uu____13016) in
                   FStar_SMTEncoding_Term.Assume uu____13007 in
                 [uu____13006] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,r,uu____13024,quals,uu____13026)
          when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13034 =
            FStar_Util.fold_map
              (fun env  ->
                 fun lb  ->
                   let lid =
                     let uu____13041 =
                       let uu____13046 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13046.FStar_Syntax_Syntax.fv_name in
                     uu____13041.FStar_Syntax_Syntax.v in
                   let uu____13050 =
                     let uu____13051 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13051 in
                   match uu____13050 with
                   | true  ->
                       let val_decl =
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp), quals, r) in
                       let uu____13070 = encode_sigelt' env val_decl in
                       (match uu____13070 with | (decls,env) -> (env, decls))
                   | uu____13077 -> (env, [])) env (Prims.snd lbs) in
          (match uu____13034 with
           | (env,decls) -> ((FStar_List.flatten decls), env))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13087,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t;
                          FStar_Syntax_Syntax.lbunivs = uu____13089;
                          FStar_Syntax_Syntax.lbtyp = uu____13090;
                          FStar_Syntax_Syntax.lbeff = uu____13091;
                          FStar_Syntax_Syntax.lbdef = uu____13092;_}::[]),uu____13093,uu____13094,uu____13095,uu____13096)
          when FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid
          ->
          let uu____13112 =
            new_term_constant_and_tok_from_lid env
              (b2t.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13112 with
           | (tname,ttok,env) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let valid_b2t_x =
                 let uu____13130 =
                   let uu____13134 =
                     let uu____13136 =
                       FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
                     [uu____13136] in
                   ("Valid", uu____13134) in
                 FStar_SMTEncoding_Util.mkApp uu____13130 in
               let decls =
                 let uu____13141 =
                   let uu____13143 =
                     let uu____13144 =
                       let uu____13149 =
                         let uu____13150 =
                           let uu____13156 =
                             let uu____13157 =
                               let uu____13160 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13160) in
                             FStar_SMTEncoding_Util.mkEq uu____13157 in
                           ([[valid_b2t_x]], [xx], uu____13156) in
                         FStar_SMTEncoding_Util.mkForall uu____13150 in
                       (uu____13149, (Some "b2t def"), (Some "b2t_def")) in
                     FStar_SMTEncoding_Term.Assume uu____13144 in
                   [uu____13143] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13141 in
               (decls, env))
      | FStar_Syntax_Syntax.Sig_let
          (uu____13178,uu____13179,uu____13180,quals,uu____13182) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___127_13190  ->
                  match uu___127_13190 with
                  | FStar_Syntax_Syntax.Discriminator uu____13191 -> true
                  | uu____13192 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          (uu____13194,uu____13195,lids,quals,uu____13198) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13207 =
                     let uu____13208 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13208.FStar_Ident.idText in
                   uu____13207 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___128_13210  ->
                     match uu___128_13210 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13211 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13214,uu____13215,quals,uu____13217) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___129_13229  ->
                  match uu___129_13229 with
                  | FStar_Syntax_Syntax.Projector uu____13230 -> true
                  | uu____13233 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13240 = try_lookup_free_var env l in
          (match uu____13240 with
           | Some uu____13244 -> ([], env)
           | None  ->
               let se =
                 FStar_Syntax_Syntax.Sig_declare_typ
                   (l, (lb.FStar_Syntax_Syntax.lbunivs),
                     (lb.FStar_Syntax_Syntax.lbtyp), quals,
                     (FStar_Ident.range_of_lid l)) in
               encode_sigelt env se)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13252,uu____13253,quals,uu____13255) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
          ->
          let uu____13267 =
            let uu____13268 =
              FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef in
            uu____13268.FStar_Syntax_Syntax.n in
          (match uu____13267 with
           | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____13275) ->
               let body = FStar_Syntax_Util.mk_reify body in
               let tm =
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_abs (bs, body, None))) None
                   (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.pos in
               let tm' =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Reify;
                   FStar_TypeChecker_Normalize.Eager_unfolding;
                   FStar_TypeChecker_Normalize.EraseUniverses;
                   FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                   env.tcenv tm in
               let lb_typ =
                 let uu____13332 =
                   FStar_Syntax_Util.arrow_formals_comp
                     lb.FStar_Syntax_Syntax.lbtyp in
                 match uu____13332 with
                 | (formals,comp) ->
                     let reified_typ =
                       FStar_TypeChecker_Util.reify_comp
                         (let uu___155_13349 = env.tcenv in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___155_13349.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___155_13349.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___155_13349.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___155_13349.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___155_13349.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___155_13349.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___155_13349.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___155_13349.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___155_13349.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___155_13349.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___155_13349.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___155_13349.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___155_13349.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___155_13349.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___155_13349.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___155_13349.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___155_13349.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___155_13349.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___155_13349.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.type_of =
                              (uu___155_13349.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___155_13349.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___155_13349.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qname_and_index =
                              (uu___155_13349.FStar_TypeChecker_Env.qname_and_index)
                          }) (FStar_Syntax_Util.lcomp_of_comp comp)
                         FStar_Syntax_Syntax.U_unknown in
                     let uu____13350 =
                       FStar_Syntax_Syntax.mk_Total reified_typ in
                     FStar_Syntax_Util.arrow formals uu____13350 in
               let lb =
                 let uu___156_13354 = lb in
                 {
                   FStar_Syntax_Syntax.lbname =
                     (uu___156_13354.FStar_Syntax_Syntax.lbname);
                   FStar_Syntax_Syntax.lbunivs =
                     (uu___156_13354.FStar_Syntax_Syntax.lbunivs);
                   FStar_Syntax_Syntax.lbtyp = lb_typ;
                   FStar_Syntax_Syntax.lbeff =
                     (uu___156_13354.FStar_Syntax_Syntax.lbeff);
                   FStar_Syntax_Syntax.lbdef = tm'
                 } in
               encode_top_level_let env (false, [lb]) quals
           | uu____13356 -> ([], env))
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13360,uu____13361,quals,uu____13363) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle
          (ses,uu____13377,uu____13378,uu____13379) ->
          let uu____13386 = encode_signature env ses in
          (match uu____13386 with
           | (g,env) ->
               let uu____13396 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___130_13406  ->
                         match uu___130_13406 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13407,Some "inversion axiom",uu____13408)
                             -> false
                         | uu____13412 -> true)) in
               (match uu____13396 with
                | (g',inversions) ->
                    let uu____13421 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___131_13431  ->
                              match uu___131_13431 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13432 ->
                                  true
                              | uu____13438 -> false)) in
                    (match uu____13421 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13449,tps,k,uu____13452,datas,quals,uu____13455) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___132_13464  ->
                    match uu___132_13464 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13465 -> false)) in
          let constructor_or_logic_type_decl c =
            match is_logical with
            | true  ->
                let uu____13472 = c in
                (match uu____13472 with
                 | (name,args,uu____13476,uu____13477,uu____13478) ->
                     let uu____13481 =
                       let uu____13482 =
                         let uu____13488 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____13495  ->
                                   match uu____13495 with
                                   | (uu____13499,sort,uu____13501) -> sort)) in
                         (name, uu____13488,
                           FStar_SMTEncoding_Term.Term_sort, None) in
                       FStar_SMTEncoding_Term.DeclFun uu____13482 in
                     [uu____13481])
            | uu____13504 -> FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13519 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13522 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13522 FStar_Option.isNone)) in
            match uu____13519 with
            | true  -> []
            | uu____13532 ->
                let uu____13533 =
                  fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
                (match uu____13533 with
                 | (xxsym,xx) ->
                     let uu____13539 =
                       FStar_All.pipe_right datas
                         (FStar_List.fold_left
                            (fun uu____13550  ->
                               fun l  ->
                                 match uu____13550 with
                                 | (out,decls) ->
                                     let uu____13562 =
                                       FStar_TypeChecker_Env.lookup_datacon
                                         env.tcenv l in
                                     (match uu____13562 with
                                      | (uu____13568,data_t) ->
                                          let uu____13570 =
                                            FStar_Syntax_Util.arrow_formals
                                              data_t in
                                          (match uu____13570 with
                                           | (args,res) ->
                                               let indices =
                                                 let uu____13599 =
                                                   let uu____13600 =
                                                     FStar_Syntax_Subst.compress
                                                       res in
                                                   uu____13600.FStar_Syntax_Syntax.n in
                                                 match uu____13599 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____13608,indices) ->
                                                     indices
                                                 | uu____13624 -> [] in
                                               let env =
                                                 FStar_All.pipe_right args
                                                   (FStar_List.fold_left
                                                      (fun env  ->
                                                         fun uu____13636  ->
                                                           match uu____13636
                                                           with
                                                           | (x,uu____13640)
                                                               ->
                                                               let uu____13641
                                                                 =
                                                                 let uu____13642
                                                                   =
                                                                   let uu____13646
                                                                    =
                                                                    mk_term_projector_name
                                                                    l x in
                                                                   (uu____13646,
                                                                    [xx]) in
                                                                 FStar_SMTEncoding_Util.mkApp
                                                                   uu____13642 in
                                                               push_term_var
                                                                 env x
                                                                 uu____13641)
                                                      env) in
                                               let uu____13648 =
                                                 encode_args indices env in
                                               (match uu____13648 with
                                                | (indices,decls') ->
                                                    ((match (FStar_List.length
                                                               indices)
                                                              <>
                                                              (FStar_List.length
                                                                 vars)
                                                      with
                                                      | true  ->
                                                          failwith
                                                            "Impossible"
                                                      | uu____13666 -> ());
                                                     (let eqs =
                                                        let uu____13668 =
                                                          FStar_List.map2
                                                            (fun v  ->
                                                               fun a  ->
                                                                 let uu____13676
                                                                   =
                                                                   let uu____13679
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v in
                                                                   (uu____13679,
                                                                    a) in
                                                                 FStar_SMTEncoding_Util.mkEq
                                                                   uu____13676)
                                                            vars indices in
                                                        FStar_All.pipe_right
                                                          uu____13668
                                                          FStar_SMTEncoding_Util.mk_and_l in
                                                      let uu____13681 =
                                                        let uu____13682 =
                                                          let uu____13685 =
                                                            let uu____13686 =
                                                              let uu____13689
                                                                =
                                                                mk_data_tester
                                                                  env l xx in
                                                              (uu____13689,
                                                                eqs) in
                                                            FStar_SMTEncoding_Util.mkAnd
                                                              uu____13686 in
                                                          (out, uu____13685) in
                                                        FStar_SMTEncoding_Util.mkOr
                                                          uu____13682 in
                                                      (uu____13681,
                                                        (FStar_List.append
                                                           decls decls'))))))))
                            (FStar_SMTEncoding_Util.mkFalse, [])) in
                     (match uu____13539 with
                      | (data_ax,decls) ->
                          let uu____13697 =
                            fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                          (match uu____13697 with
                           | (ffsym,ff) ->
                               let fuel_guarded_inversion =
                                 let xx_has_type_sfuel =
                                   match (FStar_List.length datas) >
                                           (Prims.parse_int "1")
                                   with
                                   | true  ->
                                       let uu____13708 =
                                         FStar_SMTEncoding_Util.mkApp
                                           ("SFuel", [ff]) in
                                       FStar_SMTEncoding_Term.mk_HasTypeFuel
                                         uu____13708 xx tapp
                                   | uu____13710 ->
                                       FStar_SMTEncoding_Term.mk_HasTypeFuel
                                         ff xx tapp in
                                 let uu____13711 =
                                   let uu____13716 =
                                     let uu____13717 =
                                       let uu____13723 =
                                         add_fuel
                                           (ffsym,
                                             FStar_SMTEncoding_Term.Fuel_sort)
                                           ((xxsym,
                                              FStar_SMTEncoding_Term.Term_sort)
                                           :: vars) in
                                       let uu____13731 =
                                         FStar_SMTEncoding_Util.mkImp
                                           (xx_has_type_sfuel, data_ax) in
                                       ([[xx_has_type_sfuel]], uu____13723,
                                         uu____13731) in
                                     FStar_SMTEncoding_Util.mkForall
                                       uu____13717 in
                                   let uu____13739 =
                                     let uu____13741 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "fuel_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     Some uu____13741 in
                                   (uu____13716, (Some "inversion axiom"),
                                     uu____13739) in
                                 FStar_SMTEncoding_Term.Assume uu____13711 in
                               let pattern_guarded_inversion =
                                 let uu____13746 =
                                   (contains_name env "Prims.inversion") &&
                                     ((FStar_List.length datas) >
                                        (Prims.parse_int "1")) in
                                 match uu____13746 with
                                 | true  ->
                                     let xx_has_type_fuel =
                                       FStar_SMTEncoding_Term.mk_HasTypeFuel
                                         ff xx tapp in
                                     let pattern_guard =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("Prims.inversion", [tapp]) in
                                     let uu____13754 =
                                       let uu____13755 =
                                         let uu____13760 =
                                           let uu____13761 =
                                             let uu____13767 =
                                               add_fuel
                                                 (ffsym,
                                                   FStar_SMTEncoding_Term.Fuel_sort)
                                                 ((xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 :: vars) in
                                             let uu____13775 =
                                               FStar_SMTEncoding_Util.mkImp
                                                 (xx_has_type_fuel, data_ax) in
                                             ([[xx_has_type_fuel;
                                               pattern_guard]], uu____13767,
                                               uu____13775) in
                                           FStar_SMTEncoding_Util.mkForall
                                             uu____13761 in
                                         let uu____13783 =
                                           let uu____13785 =
                                             varops.mk_unique
                                               (Prims.strcat
                                                  "pattern_guarded_inversion_"
                                                  t.FStar_Ident.str) in
                                           Some uu____13785 in
                                         (uu____13760,
                                           (Some "inversion axiom"),
                                           uu____13783) in
                                       FStar_SMTEncoding_Term.Assume
                                         uu____13755 in
                                     [uu____13754]
                                 | uu____13788 -> [] in
                               FStar_List.append decls
                                 (FStar_List.append [fuel_guarded_inversion]
                                    pattern_guarded_inversion)))) in
          let uu____13789 =
            let uu____13797 =
              let uu____13798 = FStar_Syntax_Subst.compress k in
              uu____13798.FStar_Syntax_Syntax.n in
            match uu____13797 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13827 -> (tps, k) in
          (match uu____13789 with
           | (formals,res) ->
               let uu____13842 = FStar_Syntax_Subst.open_term formals res in
               (match uu____13842 with
                | (formals,res) ->
                    let uu____13849 = encode_binders None formals env in
                    (match uu____13849 with
                     | (vars,guards,env',binder_decls,uu____13864) ->
                         let uu____13871 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____13871 with
                          | (tname,ttok,env) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____13884 =
                                  let uu____13888 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____13888) in
                                FStar_SMTEncoding_Util.mkApp uu____13884 in
                              let uu____13893 =
                                let tname_decl =
                                  let uu____13899 =
                                    let uu____13900 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____13915  ->
                                              match uu____13915 with
                                              | (n,s) ->
                                                  ((Prims.strcat tname n), s,
                                                    false))) in
                                    let uu____13923 = varops.next_id () in
                                    (tname, uu____13900,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____13923, false) in
                                  constructor_or_logic_type_decl uu____13899 in
                                let uu____13928 =
                                  match vars with
                                  | [] ->
                                      let uu____13935 =
                                        let uu____13936 =
                                          let uu____13938 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____13938 in
                                        push_free_var env t tname uu____13936 in
                                      ([], uu____13935)
                                  | uu____13942 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____13948 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____13948 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____13957 =
                                          let uu____13962 =
                                            let uu____13963 =
                                              let uu____13971 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____13971) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____13963 in
                                          (uu____13962,
                                            (Some "name-token correspondence"),
                                            (Some
                                               (Prims.strcat
                                                  "token_correspondence_"
                                                  ttok))) in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____13957 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env) in
                                match uu____13928 with
                                | (tok_decls,env) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env) in
                              (match uu____13893 with
                               | (decls,env) ->
                                   let kindingAx =
                                     let uu____13995 =
                                       encode_term_pred None res env' tapp in
                                     match uu____13995 with
                                     | (k,decls) ->
                                         let karr =
                                           match (FStar_List.length formals)
                                                   > (Prims.parse_int "0")
                                           with
                                           | true  ->
                                               let uu____14009 =
                                                 let uu____14010 =
                                                   let uu____14015 =
                                                     let uu____14016 =
                                                       FStar_SMTEncoding_Term.mk_PreType
                                                         ttok_tm in
                                                     FStar_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu____14016 in
                                                   (uu____14015,
                                                     (Some "kinding"),
                                                     (Some
                                                        (Prims.strcat
                                                           "pre_kinding_"
                                                           ttok))) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____14010 in
                                               [uu____14009]
                                           | uu____14019 -> [] in
                                         let uu____14020 =
                                           let uu____14022 =
                                             let uu____14024 =
                                               let uu____14025 =
                                                 let uu____14030 =
                                                   let uu____14031 =
                                                     let uu____14037 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k) in
                                                     ([[tapp]], vars,
                                                       uu____14037) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14031 in
                                                 (uu____14030, None,
                                                   (Some
                                                      (Prims.strcat
                                                         "kinding_" ttok))) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14025 in
                                             [uu____14024] in
                                           FStar_List.append karr uu____14022 in
                                         FStar_List.append decls uu____14020 in
                                   let aux =
                                     let uu____14047 =
                                       let uu____14049 =
                                         inversion_axioms tapp vars in
                                       let uu____14051 =
                                         let uu____14053 =
                                           pretype_axiom tapp vars in
                                         [uu____14053] in
                                       FStar_List.append uu____14049
                                         uu____14051 in
                                     FStar_List.append kindingAx uu____14047 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14058,uu____14059,uu____14060,uu____14061,uu____14062,uu____14063,uu____14064)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14071,t,uu____14073,n_tps,quals,uu____14076,drange) ->
          let uu____14082 = new_term_constant_and_tok_from_lid env d in
          (match uu____14082 with
           | (ddconstrsym,ddtok,env) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14093 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14093 with
                | (formals,t_res) ->
                    let uu____14115 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14115 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14124 =
                           encode_binders (Some fuel_tm) formals env in
                         (match uu____14124 with
                          | (vars,guards,env',binder_decls,names) ->
                              let fields =
                                FStar_All.pipe_right names
                                  (FStar_List.mapi
                                     (fun n  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14162 =
                                            mk_term_projector_name d x in
                                          (uu____14162,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14164 =
                                  let uu____14174 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14174, true) in
                                FStar_All.pipe_right uu____14164
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
                              let uu____14196 =
                                encode_term_pred None t env ddtok_tm in
                              (match uu____14196 with
                               | (tok_typing,decls3) ->
                                   let uu____14203 =
                                     encode_binders (Some fuel_tm) formals
                                       env in
                                   (match uu____14203 with
                                    | (vars',guards',env'',decls_formals,uu____14218)
                                        ->
                                        let uu____14225 =
                                          let xvars =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp in
                                        (match uu____14225 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14244 ->
                                                   let uu____14248 =
                                                     let uu____14249 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14249 in
                                                   [uu____14248] in
                                             let encode_elim uu____14256 =
                                               let uu____14257 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14257 with
                                               | (head,args) ->
                                                   let uu____14286 =
                                                     let uu____14287 =
                                                       FStar_Syntax_Subst.compress
                                                         head in
                                                     uu____14287.FStar_Syntax_Syntax.n in
                                                   (match uu____14286 with
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
                                                        let uu____14305 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14305
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               arg xv =
                                                               let fv =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv -> fv
                                                                 | uu____14331
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14339
                                                                    =
                                                                    let uu____14340
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv
                                                                    uu____14340 in
                                                                    match uu____14339
                                                                    with
                                                                    | 
                                                                    true  ->
                                                                    let uu____14347
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv xv in
                                                                    [uu____14347]
                                                                    | 
                                                                    uu____14348
                                                                    -> [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards in
                                                             let uu____14349
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14362
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14362
                                                                    with
                                                                    | 
                                                                    (env,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14384
                                                                    =
                                                                    let uu____14388
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env
                                                                    uu____14388 in
                                                                    (match uu____14384
                                                                    with
                                                                    | 
                                                                    (uu____14395,xv,env)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    match 
                                                                    i < n_tps
                                                                    with
                                                                    | 
                                                                    true  ->
                                                                    let uu____14401
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14401
                                                                    ::
                                                                    eqns_or_guards
                                                                    | 
                                                                    uu____14402
                                                                    ->
                                                                    let uu____14403
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14403
                                                                    ::
                                                                    eqns_or_guards in
                                                                    (env, (xv
                                                                    ::
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
                                                             (match uu____14349
                                                              with
                                                              | (uu____14411,arg_vars,elim_eqns_or_guards,uu____14414)
                                                                  ->
                                                                  let arg_vars
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars) in
                                                                  let xvars =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                  let dapp =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars) in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (Some
                                                                    s_fuel_tm)
                                                                    dapp ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____14433
                                                                    =
                                                                    let uu____14438
                                                                    =
                                                                    let uu____14439
                                                                    =
                                                                    let uu____14445
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14451
                                                                    =
                                                                    let uu____14452
                                                                    =
                                                                    let uu____14455
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14455) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14452 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14445,
                                                                    uu____14451) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14439 in
                                                                    (uu____14438,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14433 in
                                                                  let subterm_ordering
                                                                    =
                                                                    match 
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    with
                                                                    | 
                                                                    true  ->
                                                                    let x =
                                                                    let uu____14469
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14469,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14471
                                                                    =
                                                                    let uu____14476
                                                                    =
                                                                    let uu____14477
                                                                    =
                                                                    let uu____14483
                                                                    =
                                                                    let uu____14486
                                                                    =
                                                                    let uu____14488
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp in
                                                                    [uu____14488] in
                                                                    [uu____14486] in
                                                                    let uu____14491
                                                                    =
                                                                    let uu____14492
                                                                    =
                                                                    let uu____14495
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14496
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp in
                                                                    (uu____14495,
                                                                    uu____14496) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14492 in
                                                                    (uu____14483,
                                                                    [x],
                                                                    uu____14491) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14477 in
                                                                    let uu____14506
                                                                    =
                                                                    let uu____14508
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    Some
                                                                    uu____14508 in
                                                                    (uu____14476,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14506) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14471
                                                                    | 
                                                                    uu____14511
                                                                    ->
                                                                    let prec
                                                                    =
                                                                    let uu____14514
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v  ->
                                                                    match 
                                                                    i < n_tps
                                                                    with
                                                                    | 
                                                                    true  ->
                                                                    []
                                                                    | 
                                                                    uu____14528
                                                                    ->
                                                                    let uu____14529
                                                                    =
                                                                    let uu____14530
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14530
                                                                    dapp in
                                                                    [uu____14529])) in
                                                                    FStar_All.pipe_right
                                                                    uu____14514
                                                                    FStar_List.flatten in
                                                                    let uu____14534
                                                                    =
                                                                    let uu____14539
                                                                    =
                                                                    let uu____14540
                                                                    =
                                                                    let uu____14546
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14552
                                                                    =
                                                                    let uu____14553
                                                                    =
                                                                    let uu____14556
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14556) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14553 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14546,
                                                                    uu____14552) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14540 in
                                                                    (uu____14539,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14534 in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14567 ->
                                                        ((let uu____14569 =
                                                            let uu____14570 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14571 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14570
                                                              uu____14571 in
                                                          FStar_Errors.warn
                                                            drange
                                                            uu____14569);
                                                         ([], []))) in
                                             let uu____14574 = encode_elim () in
                                             (match uu____14574 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14586 =
                                                      let uu____14588 =
                                                        let uu____14590 =
                                                          let uu____14592 =
                                                            let uu____14594 =
                                                              let uu____14595
                                                                =
                                                                let uu____14601
                                                                  =
                                                                  let uu____14603
                                                                    =
                                                                    let uu____14604
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14604 in
                                                                  Some
                                                                    uu____14603 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14601) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14595 in
                                                            [uu____14594] in
                                                          let uu____14607 =
                                                            let uu____14609 =
                                                              let uu____14611
                                                                =
                                                                let uu____14613
                                                                  =
                                                                  let uu____14615
                                                                    =
                                                                    let uu____14617
                                                                    =
                                                                    let uu____14619
                                                                    =
                                                                    let uu____14620
                                                                    =
                                                                    let uu____14625
                                                                    =
                                                                    let uu____14626
                                                                    =
                                                                    let uu____14632
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14632) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14626 in
                                                                    (uu____14625,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14620 in
                                                                    let uu____14640
                                                                    =
                                                                    let uu____14642
                                                                    =
                                                                    let uu____14643
                                                                    =
                                                                    let uu____14648
                                                                    =
                                                                    let uu____14649
                                                                    =
                                                                    let uu____14655
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14661
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14655,
                                                                    uu____14661) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14649 in
                                                                    (uu____14648,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14643 in
                                                                    [uu____14642] in
                                                                    uu____14619
                                                                    ::
                                                                    uu____14640 in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))))
                                                                    ::
                                                                    uu____14617 in
                                                                  FStar_List.append
                                                                    uu____14615
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14613 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14611 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14609 in
                                                          FStar_List.append
                                                            uu____14592
                                                            uu____14607 in
                                                        FStar_List.append
                                                          decls3 uu____14590 in
                                                      FStar_List.append
                                                        decls2 uu____14588 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14586 in
                                                  ((FStar_List.append
                                                      datacons g), env)))))))))
and encode_signature:
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____14684  ->
              fun se  ->
                match uu____14684 with
                | (g,env) ->
                    let uu____14696 = encode_sigelt env se in
                    (match uu____14696 with
                     | (g',env) -> ((FStar_List.append g g'), env)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14732 =
        match uu____14732 with
        | (i,decls,env) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14750 ->
                 ((i + (Prims.parse_int "1")), [], env)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14755 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   match uu____14755 with
                   | true  ->
                       let uu____14756 = FStar_Syntax_Print.bv_to_string x in
                       let uu____14757 =
                         FStar_Syntax_Print.term_to_string
                           x.FStar_Syntax_Syntax.sort in
                       let uu____14758 = FStar_Syntax_Print.term_to_string t1 in
                       FStar_Util.print3 "Normalized %s : %s to %s\n"
                         uu____14756 uu____14757 uu____14758
                   | uu____14759 -> ());
                  (let uu____14760 = encode_term t1 env in
                   match uu____14760 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14770 =
                         let uu____14774 =
                           let uu____14775 =
                             let uu____14776 =
                               FStar_Util.digest_of_string t_hash in
                             let uu____14777 =
                               let uu____14778 = FStar_Util.string_of_int i in
                               Prims.strcat "_" uu____14778 in
                             Prims.strcat uu____14776 uu____14777 in
                           Prims.strcat "x_" uu____14775 in
                         new_term_constant_from_string env x uu____14774 in
                       (match uu____14770 with
                        | (xxsym,xx,env') ->
                            let t =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____14789 = FStar_Options.log_queries () in
                              match uu____14789 with
                              | true  ->
                                  let uu____14791 =
                                    let uu____14792 =
                                      FStar_Syntax_Print.bv_to_string x in
                                    let uu____14793 =
                                      FStar_Syntax_Print.term_to_string
                                        x.FStar_Syntax_Syntax.sort in
                                    let uu____14794 =
                                      FStar_Syntax_Print.term_to_string t1 in
                                    FStar_Util.format3 "%s : %s (%s)"
                                      uu____14792 uu____14793 uu____14794 in
                                  Some uu____14791
                              | uu____14795 -> None in
                            let ax =
                              let a_name =
                                Some (Prims.strcat "binder_" xxsym) in
                              FStar_SMTEncoding_Term.Assume
                                (t, a_name, a_name) in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax]) in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14807,t)) ->
                 let t_norm = whnf env t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____14816 = encode_free_var env fv t t_norm [] in
                 (match uu____14816 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____14835 = encode_sigelt env se in
                 (match uu____14835 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____14845 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____14845 with | (uu____14857,decls,env) -> (decls, env)
let encode_labels labs =
  let prefix =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____14902  ->
            match uu____14902 with
            | (l,uu____14909,uu____14910) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____14931  ->
            match uu____14931 with
            | (l,uu____14939,uu____14940) ->
                let uu____14945 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____14946 =
                  let uu____14948 =
                    let uu____14949 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____14949 in
                  [uu____14948] in
                uu____14945 :: uu____14946)) in
  (prefix, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____14960 =
      let uu____14962 =
        let uu____14963 = FStar_Util.smap_create (Prims.parse_int "100") in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____14963;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true
        } in
      [uu____14962] in
    FStar_ST.write last_env uu____14960
let get_env: FStar_TypeChecker_Env.env -> env_t =
  fun tcenv  ->
    let uu____14981 = FStar_ST.read last_env in
    match uu____14981 with
    | [] -> failwith "No env; call init first!"
    | e::uu____14987 ->
        let uu___157_14989 = e in
        {
          bindings = (uu___157_14989.bindings);
          depth = (uu___157_14989.depth);
          tcenv;
          warn = (uu___157_14989.warn);
          cache = (uu___157_14989.cache);
          nolabels = (uu___157_14989.nolabels);
          use_zfuel_name = (uu___157_14989.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___157_14989.encode_non_total_function_typ)
        }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____14993 = FStar_ST.read last_env in
    match uu____14993 with
    | [] -> failwith "Empty env stack"
    | uu____14998::tl -> FStar_ST.write last_env (env :: tl)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15006  ->
    let uu____15007 = FStar_ST.read last_env in
    match uu____15007 with
    | [] -> failwith "Empty env stack"
    | hd::tl ->
        let refs = FStar_Util.smap_copy hd.cache in
        let top =
          let uu___158_15028 = hd in
          {
            bindings = (uu___158_15028.bindings);
            depth = (uu___158_15028.depth);
            tcenv = (uu___158_15028.tcenv);
            warn = (uu___158_15028.warn);
            cache = refs;
            nolabels = (uu___158_15028.nolabels);
            use_zfuel_name = (uu___158_15028.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___158_15028.encode_non_total_function_typ)
          } in
        FStar_ST.write last_env (top :: hd :: tl)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15034  ->
    let uu____15035 = FStar_ST.read last_env in
    match uu____15035 with
    | [] -> failwith "Popping an empty stack"
    | uu____15040::tl -> FStar_ST.write last_env tl
let mark_env: Prims.unit -> Prims.unit = fun uu____15048  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15051  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15054  ->
    let uu____15055 = FStar_ST.read last_env in
    match uu____15055 with
    | hd::uu____15061::tl -> FStar_ST.write last_env (hd :: tl)
    | uu____15067 -> failwith "Impossible"
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
        let uu____15112 = FStar_Options.log_queries () in
        match uu____15112 with
        | true  ->
            let uu____15114 =
              let uu____15115 =
                let uu____15116 =
                  let uu____15117 =
                    FStar_All.pipe_right
                      (FStar_Syntax_Util.lids_of_sigelt se)
                      (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                  FStar_All.pipe_right uu____15117 (FStar_String.concat ", ") in
                Prims.strcat "encoding sigelt " uu____15116 in
              FStar_SMTEncoding_Term.Caption uu____15115 in
            uu____15114 :: decls
        | uu____15122 -> decls in
      let env = get_env tcenv in
      let uu____15124 = encode_sigelt env se in
      match uu____15124 with
      | (decls,env) ->
          (set_env env;
           (let uu____15130 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15130))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (match modul.FStar_Syntax_Syntax.is_interface with
           | true  -> "interface"
           | uu____15139 -> "module")
          (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15141 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       match uu____15141 with
       | true  ->
           let uu____15142 =
             FStar_All.pipe_right
               (FStar_List.length modul.FStar_Syntax_Syntax.exports)
               FStar_Util.string_of_int in
           FStar_Util.print2
             "+++++++++++Encoding externals for %s ... %s exports\n" name
             uu____15142
       | uu____15145 -> ());
      (let env = get_env tcenv in
       let uu____15147 =
         encode_signature
           (let uu___159_15151 = env in
            {
              bindings = (uu___159_15151.bindings);
              depth = (uu___159_15151.depth);
              tcenv = (uu___159_15151.tcenv);
              warn = false;
              cache = (uu___159_15151.cache);
              nolabels = (uu___159_15151.nolabels);
              use_zfuel_name = (uu___159_15151.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___159_15151.encode_non_total_function_typ)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15147 with
       | (decls,env) ->
           let caption decls =
             let uu____15163 = FStar_Options.log_queries () in
             match uu____15163 with
             | true  ->
                 let msg = Prims.strcat "Externals for " name in
                 FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                   decls)
                   [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             | uu____15166 -> decls in
           (set_env
              (let uu___160_15168 = env in
               {
                 bindings = (uu___160_15168.bindings);
                 depth = (uu___160_15168.depth);
                 tcenv = (uu___160_15168.tcenv);
                 warn = true;
                 cache = (uu___160_15168.cache);
                 nolabels = (uu___160_15168.nolabels);
                 use_zfuel_name = (uu___160_15168.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___160_15168.encode_non_total_function_typ)
               });
            (let uu____15170 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             match uu____15170 with
             | true  ->
                 FStar_Util.print1 "Done encoding externals for %s\n" name
             | uu____15171 -> ());
            (let decls = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls)))
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
        (let uu____15205 =
           let uu____15206 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15206.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15205);
        (let env = get_env tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15214 =
           let rec aux bindings =
             match bindings with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15235 = aux rest in
                 (match uu____15235 with
                  | (out,rest) ->
                      let t =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv x.FStar_Syntax_Syntax.sort in
                      let uu____15251 =
                        let uu____15253 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___161_15254 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___161_15254.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___161_15254.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t
                             }) in
                        uu____15253 :: out in
                      (uu____15251, rest))
             | uu____15257 -> ([], bindings) in
           let uu____15261 = aux bindings in
           match uu____15261 with
           | (closing,bindings) ->
               let uu____15275 =
                 FStar_Syntax_Util.close_forall (FStar_List.rev closing) q in
               (uu____15275, bindings) in
         match uu____15214 with
         | (q,bindings) ->
             let uu____15288 =
               let uu____15291 =
                 FStar_List.filter
                   (fun uu___133_15293  ->
                      match uu___133_15293 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15294 ->
                          false
                      | uu____15298 -> true) bindings in
               encode_env_bindings env uu____15291 in
             (match uu____15288 with
              | (env_decls,env) ->
                  ((let uu____15309 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    match uu____15309 with
                    | true  ->
                        let uu____15310 = FStar_Syntax_Print.term_to_string q in
                        FStar_Util.print1 "Encoding query formula: %s\n"
                          uu____15310
                    | uu____15311 -> ());
                   (let uu____15312 = encode_formula q env in
                    match uu____15312 with
                    | (phi,qdecls) ->
                        let uu____15324 =
                          let uu____15327 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15327 phi in
                        (match uu____15324 with
                         | (labels,phi) ->
                             let uu____15337 = encode_labels labels in
                             (match uu____15337 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15358 =
                                      let uu____15363 =
                                        FStar_SMTEncoding_Util.mkNot phi in
                                      let uu____15364 =
                                        let uu____15366 =
                                          varops.mk_unique "@query" in
                                        Some uu____15366 in
                                      (uu____15363, (Some "query"),
                                        uu____15364) in
                                    FStar_SMTEncoding_Term.Assume uu____15358 in
                                  let suffix =
                                    let uu____15371 =
                                      let uu____15373 =
                                        let uu____15375 =
                                          FStar_Options.print_z3_statistics
                                            () in
                                        match uu____15375 with
                                        | true  ->
                                            [FStar_SMTEncoding_Term.PrintStats]
                                        | uu____15377 -> [] in
                                      FStar_List.append uu____15373
                                        [FStar_SMTEncoding_Term.Echo "Done!"] in
                                    FStar_List.append label_suffix
                                      uu____15371 in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env = get_env tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15388 = encode_formula q env in
       match uu____15388 with
       | (f,uu____15392) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15394) -> true
             | uu____15397 -> false)))