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
          let a2 = unmangle a in
          let uu____1092 = aux a2 in
          (match uu____1092 with
           | None  ->
               let uu____1098 =
                 let uu____1099 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1100 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1099 uu____1100 in
               failwith uu____1098
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1120 =
        let uu___140_1121 = env in
        let uu____1122 =
          let uu____1124 =
            let uu____1125 =
              let uu____1132 =
                let uu____1134 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1134 in
              (x, fname, uu____1132, None) in
            Binding_fvar uu____1125 in
          uu____1124 :: (env.bindings) in
        {
          bindings = uu____1122;
          depth = (uu___140_1121.depth);
          tcenv = (uu___140_1121.tcenv);
          warn = (uu___140_1121.warn);
          cache = (uu___140_1121.cache);
          nolabels = (uu___140_1121.nolabels);
          use_zfuel_name = (uu___140_1121.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___140_1121.encode_non_total_function_typ)
        } in
      (fname, ftok, uu____1120)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___112_1156  ->
           match uu___112_1156 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1178 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1190 =
        lookup_binding env
          (fun uu___113_1192  ->
             match uu___113_1192 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1202 -> None) in
      FStar_All.pipe_right uu____1190 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1215 = try_lookup_lid env a in
      match uu____1215 with
      | None  ->
          let uu____1232 =
            let uu____1233 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1233 in
          failwith uu____1232
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
          let uu___141_1264 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___141_1264.depth);
            tcenv = (uu___141_1264.tcenv);
            warn = (uu___141_1264.warn);
            cache = (uu___141_1264.cache);
            nolabels = (uu___141_1264.nolabels);
            use_zfuel_name = (uu___141_1264.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___141_1264.encode_non_total_function_typ)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1276 = lookup_lid env x in
        match uu____1276 with
        | (t1,t2,uu____1284) ->
            let t3 =
              let uu____1290 =
                let uu____1294 =
                  let uu____1296 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1296] in
                (f, uu____1294) in
              FStar_SMTEncoding_Util.mkApp uu____1290 in
            let uu___142_1299 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___142_1299.depth);
              tcenv = (uu___142_1299.tcenv);
              warn = (uu___142_1299.warn);
              cache = (uu___142_1299.cache);
              nolabels = (uu___142_1299.nolabels);
              use_zfuel_name = (uu___142_1299.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___142_1299.encode_non_total_function_typ)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1309 = try_lookup_lid env l in
      match uu____1309 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1336 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1341,fuel::[]) ->
                         let uu____1344 =
                           let uu____1345 =
                             let uu____1346 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1346 Prims.fst in
                           FStar_Util.starts_with uu____1345 "fuel" in
                         (match uu____1344 with
                          | true  ->
                              let uu____1348 =
                                let uu____1349 =
                                  FStar_SMTEncoding_Util.mkFreeV
                                    (name, FStar_SMTEncoding_Term.Term_sort) in
                                FStar_SMTEncoding_Term.mk_ApplyTF uu____1349
                                  fuel in
                              FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                                uu____1348
                          | uu____1351 -> Some t)
                     | uu____1352 -> Some t)
                | uu____1353 -> None))
let lookup_free_var env a =
  let uu____1371 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1371 with
  | Some t -> t
  | None  ->
      let uu____1374 =
        let uu____1375 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1375 in
      failwith uu____1374
let lookup_free_var_name env a =
  let uu____1392 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1392 with | (x,uu____1399,uu____1400) -> x
let lookup_free_var_sym env a =
  let uu____1424 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1424 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1445;
             FStar_SMTEncoding_Term.rng = uu____1446;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1454 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym ->
                (match sym.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1468 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___114_1477  ->
           match uu___114_1477 with
           | Binding_fvar (uu____1479,nm',tok,uu____1482) when nm = nm' ->
               tok
           | uu____1487 -> None)
let mkForall_fuel' n uu____1504 =
  match uu____1504 with
  | (pats,vars,body) ->
      let fallback uu____1520 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1523 = FStar_Options.unthrottle_inductives () in
      (match uu____1523 with
       | true  -> fallback ()
       | uu____1524 ->
           let uu____1525 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
           (match uu____1525 with
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
                          | uu____1544 -> p)) in
                let pats = FStar_List.map add_fuel pats in
                let body =
                  match body.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                      let guard =
                        match guard.FStar_SMTEncoding_Term.tm with
                        | FStar_SMTEncoding_Term.App
                            (FStar_SMTEncoding_Term.And ,guards) ->
                            let uu____1558 = add_fuel guards in
                            FStar_SMTEncoding_Util.mk_and_l uu____1558
                        | uu____1560 ->
                            let uu____1561 = add_fuel [guard] in
                            FStar_All.pipe_right uu____1561 FStar_List.hd in
                      FStar_SMTEncoding_Util.mkImp (guard, body')
                  | uu____1564 -> body in
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
          let uu____1608 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1608 FStar_Option.isNone
      | uu____1621 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1628 =
        let uu____1629 = FStar_Syntax_Util.un_uinst t in
        uu____1629.FStar_Syntax_Syntax.n in
      match uu____1628 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1632,uu____1633,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___115_1662  ->
                  match uu___115_1662 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1663 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1664,uu____1665,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1692 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1692 FStar_Option.isSome
      | uu____1705 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1712 = head_normal env t in
      match uu____1712 with
      | true  -> t
      | uu____1713 ->
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
    let uu____1723 =
      let uu____1727 = FStar_Syntax_Syntax.null_binder t in [uu____1727] in
    let uu____1728 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1723 uu____1728 None
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
                    let uu____1755 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1755
                | s ->
                    let uu____1758 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1758) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___116_1770  ->
    match uu___116_1770 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1771 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____1799;
                       FStar_SMTEncoding_Term.rng = uu____1800;_}::[]),x::xs)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              aux f xs
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1814) ->
              let uu____1819 =
                ((FStar_List.length args) = (FStar_List.length vars)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v
                          | uu____1829 -> false) args vars) in
              (match uu____1819 with
               | true  -> tok_of_name env f
               | uu____1831 -> None)
          | (uu____1832,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1835 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1837 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1837)) in
              (match uu____1835 with | true  -> Some t | uu____1839 -> None)
          | uu____1840 -> None in
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
    | uu____1924 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___117_1927  ->
    match uu___117_1927 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____1929 =
          let uu____1933 =
            let uu____1935 =
              let uu____1936 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____1936 in
            [uu____1935] in
          ("FStar.Char.Char", uu____1933) in
        FStar_SMTEncoding_Util.mkApp uu____1929
    | FStar_Const.Const_int (i,None ) ->
        let uu____1944 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____1944
    | FStar_Const.Const_int (i,Some uu____1946) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____1955) ->
        let uu____1958 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____1958
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____1962 =
          let uu____1963 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____1963 in
        failwith uu____1962
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1982 -> t
        | FStar_Syntax_Syntax.Tm_refine uu____1990 ->
            let uu____1995 = FStar_Syntax_Util.unrefine t in
            aux true uu____1995
        | uu____1996 ->
            (match norm with
             | true  -> let uu____1997 = whnf env t in aux false uu____1997
             | uu____1998 ->
                 let uu____1999 =
                   let uu____2000 =
                     FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                   let uu____2001 = FStar_Syntax_Print.term_to_string t0 in
                   FStar_Util.format2 "(%s) Expected a function typ; got %s"
                     uu____2000 uu____2001 in
                 failwith uu____1999) in
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
    | uu____2022 ->
        let uu____2023 = FStar_Syntax_Syntax.mk_Total k in ([], uu____2023)
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
        (let uu____2166 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         match uu____2166 with
         | true  ->
             let uu____2167 = FStar_Syntax_Print.binders_to_string ", " bs in
             FStar_Util.print1 "Encoding binders %s\n" uu____2167
         | uu____2168 -> ());
        (let uu____2169 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2205  ->
                   fun b  ->
                     match uu____2205 with
                     | (vars,guards,env,decls,names) ->
                         let uu____2248 =
                           let x = unmangle (Prims.fst b) in
                           let uu____2257 = gen_term_var env x in
                           match uu____2257 with
                           | (xxsym,xx,env') ->
                               let uu____2271 =
                                 let uu____2274 =
                                   norm env x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2274 env xx in
                               (match uu____2271 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2248 with
                          | (v,g,env,decls',n) ->
                              ((v :: vars), (g :: guards), env,
                                (FStar_List.append decls decls'), (n ::
                                names)))) ([], [], env, [], [])) in
         match uu____2169 with
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
          let uu____2362 = encode_term t env in
          match uu____2362 with
          | (t,decls) ->
              let uu____2369 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t in
              (uu____2369, decls)
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
          let uu____2377 = encode_term t env in
          match uu____2377 with
          | (t,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2386 = FStar_SMTEncoding_Term.mk_HasTypeZ e t in
                   (uu____2386, decls)
               | Some f ->
                   let uu____2388 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t in
                   (uu____2388, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2395 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       match uu____2395 with
       | true  ->
           let uu____2396 = FStar_Syntax_Print.tag_of_term t in
           let uu____2397 = FStar_Syntax_Print.tag_of_term t0 in
           let uu____2398 = FStar_Syntax_Print.term_to_string t0 in
           FStar_Util.print3 "(%s) (%s)   %s\n" uu____2396 uu____2397
             uu____2398
       | uu____2399 -> ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2403 =
             let uu____2404 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2405 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2406 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2407 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2404
               uu____2405 uu____2406 uu____2407 in
           failwith uu____2403
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2411 =
             let uu____2412 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2412 in
           failwith uu____2411
       | FStar_Syntax_Syntax.Tm_ascribed (t,k,uu____2417) ->
           encode_term t env
       | FStar_Syntax_Syntax.Tm_meta (t,uu____2437) -> encode_term t env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t = lookup_term_var env x in (t, [])
       | FStar_Syntax_Syntax.Tm_fvar v ->
           let uu____2446 = lookup_free_var env v.FStar_Syntax_Syntax.fv_name in
           (uu____2446, [])
       | FStar_Syntax_Syntax.Tm_type uu____2452 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t,uu____2455) -> encode_term t env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2461 = encode_const c in (uu____2461, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let uu____2475 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2475 with
            | (binders,res) ->
                let uu____2482 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                (match uu____2482 with
                 | true  ->
                     let uu____2485 = encode_binders None binders env in
                     (match uu____2485 with
                      | (vars,guards,env',decls,uu____2500) ->
                          let fsym =
                            let uu____2510 = varops.fresh "f" in
                            (uu____2510, FStar_SMTEncoding_Term.Term_sort) in
                          let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                          let app = mk_Apply f vars in
                          let uu____2513 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              (let uu___143_2517 = env.tcenv in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___143_2517.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___143_2517.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___143_2517.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___143_2517.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___143_2517.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___143_2517.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___143_2517.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___143_2517.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___143_2517.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___143_2517.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___143_2517.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___143_2517.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___143_2517.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___143_2517.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___143_2517.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___143_2517.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___143_2517.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___143_2517.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___143_2517.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___143_2517.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___143_2517.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___143_2517.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___143_2517.FStar_TypeChecker_Env.qname_and_index)
                               }) res in
                          (match uu____2513 with
                           | (pre_opt,res_t) ->
                               let uu____2524 =
                                 encode_term_pred None res_t env' app in
                               (match uu____2524 with
                                | (res_pred,decls') ->
                                    let uu____2531 =
                                      match pre_opt with
                                      | None  ->
                                          let uu____2538 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              guards in
                                          (uu____2538, [])
                                      | Some pre ->
                                          let uu____2541 =
                                            encode_formula pre env' in
                                          (match uu____2541 with
                                           | (guard,decls0) ->
                                               let uu____2549 =
                                                 FStar_SMTEncoding_Util.mk_and_l
                                                   (guard :: guards) in
                                               (uu____2549, decls0)) in
                                    (match uu____2531 with
                                     | (guards,guard_decls) ->
                                         let t_interp =
                                           let uu____2557 =
                                             let uu____2563 =
                                               FStar_SMTEncoding_Util.mkImp
                                                 (guards, res_pred) in
                                             ([[app]], vars, uu____2563) in
                                           FStar_SMTEncoding_Util.mkForall
                                             uu____2557 in
                                         let cvars =
                                           let uu____2573 =
                                             FStar_SMTEncoding_Term.free_variables
                                               t_interp in
                                           FStar_All.pipe_right uu____2573
                                             (FStar_List.filter
                                                (fun uu____2579  ->
                                                   match uu____2579 with
                                                   | (x,uu____2583) ->
                                                       x <> (Prims.fst fsym))) in
                                         let tkey =
                                           FStar_SMTEncoding_Util.mkForall
                                             ([], (fsym :: cvars), t_interp) in
                                         let tkey_hash =
                                           FStar_SMTEncoding_Term.hash_of_term
                                             tkey in
                                         let uu____2594 =
                                           FStar_Util.smap_try_find env.cache
                                             tkey_hash in
                                         (match uu____2594 with
                                          | Some (t',sorts,uu____2610) ->
                                              let uu____2620 =
                                                let uu____2621 =
                                                  let uu____2625 =
                                                    FStar_All.pipe_right
                                                      cvars
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV) in
                                                  (t', uu____2625) in
                                                FStar_SMTEncoding_Util.mkApp
                                                  uu____2621 in
                                              (uu____2620, [])
                                          | None  ->
                                              let tsym =
                                                let uu____2641 =
                                                  let uu____2642 =
                                                    FStar_Util.digest_of_string
                                                      tkey_hash in
                                                  Prims.strcat "Tm_arrow_"
                                                    uu____2642 in
                                                varops.mk_unique uu____2641 in
                                              let cvar_sorts =
                                                FStar_List.map Prims.snd
                                                  cvars in
                                              let caption =
                                                let uu____2649 =
                                                  FStar_Options.log_queries
                                                    () in
                                                match uu____2649 with
                                                | true  ->
                                                    let uu____2651 =
                                                      FStar_TypeChecker_Normalize.term_to_string
                                                        env.tcenv t0 in
                                                    Some uu____2651
                                                | uu____2652 -> None in
                                              let tdecl =
                                                FStar_SMTEncoding_Term.DeclFun
                                                  (tsym, cvar_sorts,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    caption) in
                                              let t =
                                                let uu____2657 =
                                                  let uu____2661 =
                                                    FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV
                                                      cvars in
                                                  (tsym, uu____2661) in
                                                FStar_SMTEncoding_Util.mkApp
                                                  uu____2657 in
                                              let t_has_kind =
                                                FStar_SMTEncoding_Term.mk_HasType
                                                  t
                                                  FStar_SMTEncoding_Term.mk_Term_type in
                                              let k_assumption =
                                                let a_name =
                                                  Some
                                                    (Prims.strcat "kinding_"
                                                       tsym) in
                                                let uu____2670 =
                                                  let uu____2675 =
                                                    FStar_SMTEncoding_Util.mkForall
                                                      ([[t_has_kind]], cvars,
                                                        t_has_kind) in
                                                  (uu____2675, a_name,
                                                    a_name) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____2670 in
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
                                                let uu____2690 =
                                                  let uu____2695 =
                                                    let uu____2696 =
                                                      let uu____2702 =
                                                        let uu____2703 =
                                                          let uu____2706 =
                                                            let uu____2707 =
                                                              FStar_SMTEncoding_Term.mk_PreType
                                                                f in
                                                            FStar_SMTEncoding_Term.mk_tester
                                                              "Tm_arrow"
                                                              uu____2707 in
                                                          (f_has_t,
                                                            uu____2706) in
                                                        FStar_SMTEncoding_Util.mkImp
                                                          uu____2703 in
                                                      ([[f_has_t]], (fsym ::
                                                        cvars), uu____2702) in
                                                    mkForall_fuel uu____2696 in
                                                  (uu____2695,
                                                    (Some
                                                       "pre-typing for functions"),
                                                    a_name) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____2690 in
                                              let t_interp =
                                                let a_name =
                                                  Some
                                                    (Prims.strcat
                                                       "interpretation_" tsym) in
                                                let uu____2722 =
                                                  let uu____2727 =
                                                    let uu____2728 =
                                                      let uu____2734 =
                                                        FStar_SMTEncoding_Util.mkIff
                                                          (f_has_t_z,
                                                            t_interp) in
                                                      ([[f_has_t_z]], (fsym
                                                        :: cvars),
                                                        uu____2734) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____2728 in
                                                  (uu____2727, a_name,
                                                    a_name) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____2722 in
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
                 | uu____2757 ->
                     let tsym = varops.fresh "Non_total_Tm_arrow" in
                     let tdecl =
                       FStar_SMTEncoding_Term.DeclFun
                         (tsym, [], FStar_SMTEncoding_Term.Term_sort, None) in
                     let t = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                     let t_kinding =
                       let a_name =
                         Some
                           (Prims.strcat "non_total_function_typing_" tsym) in
                       let uu____2767 =
                         let uu____2772 =
                           FStar_SMTEncoding_Term.mk_HasType t
                             FStar_SMTEncoding_Term.mk_Term_type in
                         (uu____2772, (Some "Typing for non-total arrows"),
                           a_name) in
                       FStar_SMTEncoding_Term.Assume uu____2767 in
                     let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                     let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                     let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t in
                     let t_interp =
                       let a_name = Some (Prims.strcat "pre_typing_" tsym) in
                       let uu____2783 =
                         let uu____2788 =
                           let uu____2789 =
                             let uu____2795 =
                               let uu____2796 =
                                 let uu____2799 =
                                   let uu____2800 =
                                     FStar_SMTEncoding_Term.mk_PreType f in
                                   FStar_SMTEncoding_Term.mk_tester
                                     "Tm_arrow" uu____2800 in
                                 (f_has_t, uu____2799) in
                               FStar_SMTEncoding_Util.mkImp uu____2796 in
                             ([[f_has_t]], [fsym], uu____2795) in
                           mkForall_fuel uu____2789 in
                         (uu____2788, a_name, a_name) in
                       FStar_SMTEncoding_Term.Assume uu____2783 in
                     (t, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2815 ->
           let uu____2820 =
             let uu____2823 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2823 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2828;
                 FStar_Syntax_Syntax.pos = uu____2829;
                 FStar_Syntax_Syntax.vars = uu____2830;_} ->
                 let uu____2837 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2837 with
                  | (b,f) ->
                      let uu____2851 =
                        let uu____2852 = FStar_List.hd b in
                        Prims.fst uu____2852 in
                      (uu____2851, f))
             | uu____2857 -> failwith "impossible" in
           (match uu____2820 with
            | (x,f) ->
                let uu____2864 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____2864 with
                 | (base_t,decls) ->
                     let uu____2871 = gen_term_var env x in
                     (match uu____2871 with
                      | (x,xtm,env') ->
                          let uu____2880 = encode_formula f env' in
                          (match uu____2880 with
                           | (refinement,decls') ->
                               let uu____2887 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____2887 with
                                | (fsym,fterm) ->
                                    let encoding =
                                      let uu____2895 =
                                        let uu____2898 =
                                          FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                            (Some fterm) xtm base_t in
                                        (uu____2898, refinement) in
                                      FStar_SMTEncoding_Util.mkAnd uu____2895 in
                                    let cvars =
                                      let uu____2903 =
                                        FStar_SMTEncoding_Term.free_variables
                                          encoding in
                                      FStar_All.pipe_right uu____2903
                                        (FStar_List.filter
                                           (fun uu____2909  ->
                                              match uu____2909 with
                                              | (y,uu____2913) ->
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
                                    let uu____2932 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2932 with
                                     | Some (t,uu____2947,uu____2948) ->
                                         let uu____2958 =
                                           let uu____2959 =
                                             let uu____2963 =
                                               FStar_All.pipe_right cvars
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             (t, uu____2963) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2959 in
                                         (uu____2958, [])
                                     | None  ->
                                         let tsym =
                                           let uu____2979 =
                                             let uu____2980 =
                                               FStar_Util.digest_of_string
                                                 tkey_hash in
                                             Prims.strcat "Tm_refine_"
                                               uu____2980 in
                                           varops.mk_unique uu____2979 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t =
                                           let uu____2989 =
                                             let uu____2993 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars in
                                             (tsym, uu____2993) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2989 in
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
                                           let uu____3003 =
                                             let uu____3008 =
                                               let uu____3009 =
                                                 let uu____3015 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars,
                                                   uu____3015) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3009 in
                                             (uu____3008,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Some
                                                  (Prims.strcat "haseq" tsym))) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3003 in
                                         let t_kinding =
                                           let uu____3026 =
                                             let uu____3031 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars,
                                                   t_has_kind) in
                                             (uu____3031,
                                               (Some "refinement kinding"),
                                               (Some
                                                  (Prims.strcat
                                                     "refinement_kinding_"
                                                     tsym))) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3026 in
                                         let t_interp =
                                           let uu____3042 =
                                             let uu____3047 =
                                               let uu____3048 =
                                                 let uu____3054 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars), uu____3054) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3048 in
                                             let uu____3066 =
                                               let uu____3068 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3068 in
                                             (uu____3047, uu____3066,
                                               (Some
                                                  (Prims.strcat
                                                     "refinement_interpretation_"
                                                     tsym))) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3042 in
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
             let uu____3097 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3097 in
           let uu____3101 = encode_term_pred None k env ttm in
           (match uu____3101 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3109 =
                    let uu____3114 =
                      let uu____3116 =
                        let uu____3117 =
                          let uu____3118 =
                            let uu____3119 = FStar_Unionfind.uvar_id uv in
                            FStar_All.pipe_left FStar_Util.string_of_int
                              uu____3119 in
                          FStar_Util.format1 "uvar_typing_%s" uu____3118 in
                        varops.mk_unique uu____3117 in
                      Some uu____3116 in
                    (t_has_k, (Some "Uvar typing"), uu____3114) in
                  FStar_SMTEncoding_Term.Assume uu____3109 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3126 ->
           let uu____3136 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3136 with
            | (head,args_e) ->
                let uu____3164 =
                  let uu____3172 =
                    let uu____3173 = FStar_Syntax_Subst.compress head in
                    uu____3173.FStar_Syntax_Syntax.n in
                  (uu____3172, args_e) in
                (match uu____3164 with
                 | (uu____3183,uu____3184) when head_redex env head ->
                     let uu____3195 = whnf env t in
                     encode_term uu____3195 env
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
                     let uu____3269 = encode_term v1 env in
                     (match uu____3269 with
                      | (v1,decls1) ->
                          let uu____3276 = encode_term v2 env in
                          (match uu____3276 with
                           | (v2,decls2) ->
                               let uu____3283 =
                                 FStar_SMTEncoding_Util.mk_LexCons v1 v2 in
                               (uu____3283,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3285) ->
                     let e0 =
                       let uu____3299 =
                         let uu____3302 =
                           let uu____3303 =
                             let uu____3313 =
                               let uu____3319 = FStar_List.hd args_e in
                               [uu____3319] in
                             (head, uu____3313) in
                           FStar_Syntax_Syntax.Tm_app uu____3303 in
                         FStar_Syntax_Syntax.mk uu____3302 in
                       uu____3299 None head.FStar_Syntax_Syntax.pos in
                     ((let uu____3352 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       match uu____3352 with
                       | true  ->
                           let uu____3353 =
                             FStar_Syntax_Print.term_to_string e0 in
                           FStar_Util.print1 "Trying to normalize %s\n"
                             uu____3353
                       | uu____3354 -> ());
                      (let e0 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Reify;
                           FStar_TypeChecker_Normalize.Eager_unfolding;
                           FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                           env.tcenv e0 in
                       (let uu____3357 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify") in
                        match uu____3357 with
                        | true  ->
                            let uu____3358 =
                              FStar_Syntax_Print.term_to_string e0 in
                            FStar_Util.print1 "Result of normalization %s\n"
                              uu____3358
                        | uu____3359 -> ());
                       (let e0 =
                          let uu____3361 =
                            let uu____3362 =
                              let uu____3363 = FStar_Syntax_Subst.compress e0 in
                              uu____3363.FStar_Syntax_Syntax.n in
                            match uu____3362 with
                            | FStar_Syntax_Syntax.Tm_app uu____3366 -> false
                            | uu____3376 -> true in
                          match uu____3361 with
                          | true  -> e0
                          | uu____3377 ->
                              let uu____3378 =
                                FStar_Syntax_Util.head_and_args e0 in
                              (match uu____3378 with
                               | (head,args) ->
                                   let uu____3404 =
                                     let uu____3405 =
                                       let uu____3406 =
                                         FStar_Syntax_Subst.compress head in
                                       uu____3406.FStar_Syntax_Syntax.n in
                                     match uu____3405 with
                                     | FStar_Syntax_Syntax.Tm_constant
                                         (FStar_Const.Const_reify ) -> true
                                     | uu____3409 -> false in
                                   (match uu____3404 with
                                    | true  ->
                                        (match args with
                                         | x::[] -> Prims.fst x
                                         | uu____3425 ->
                                             failwith
                                               "Impossible : Reify applied to multiple arguments after normalization.")
                                    | uu____3431 -> e0)) in
                        let e =
                          match args_e with
                          | uu____3433::[] -> e0
                          | uu____3446 ->
                              let uu____3452 =
                                let uu____3455 =
                                  let uu____3456 =
                                    let uu____3466 = FStar_List.tl args_e in
                                    (e0, uu____3466) in
                                  FStar_Syntax_Syntax.Tm_app uu____3456 in
                                FStar_Syntax_Syntax.mk uu____3455 in
                              uu____3452 None t0.FStar_Syntax_Syntax.pos in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3489),(arg,uu____3491)::[]) -> encode_term arg env
                 | uu____3509 ->
                     let uu____3517 = encode_args args_e env in
                     (match uu____3517 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3550 = encode_term head env in
                            match uu____3550 with
                            | (head,decls') ->
                                let app_tm = mk_Apply_args head args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3589 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3589 with
                                      | (formals,rest) ->
                                          let subst =
                                            FStar_List.map2
                                              (fun uu____3631  ->
                                                 fun uu____3632  ->
                                                   match (uu____3631,
                                                           uu____3632)
                                                   with
                                                   | ((bv,uu____3646),
                                                      (a,uu____3648)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals
                                              args_e in
                                          let ty =
                                            let uu____3662 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3662
                                              (FStar_Syntax_Subst.subst subst) in
                                          let uu____3667 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3667 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3677 =
                                                   let uu____3682 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3687 =
                                                     let uu____3689 =
                                                       let uu____3690 =
                                                         let uu____3691 =
                                                           let uu____3692 =
                                                             FStar_SMTEncoding_Term.hash_of_term
                                                               app_tm in
                                                           FStar_Util.digest_of_string
                                                             uu____3692 in
                                                         Prims.strcat
                                                           "partial_app_typing_"
                                                           uu____3691 in
                                                       varops.mk_unique
                                                         uu____3690 in
                                                     Some uu____3689 in
                                                   (uu____3682,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3687) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3677 in
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
                                let uu____3748 =
                                  let uu____3749 =
                                    FStar_TypeChecker_Env.lookup_lid
                                      env.tcenv
                                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                  FStar_All.pipe_right uu____3749 Prims.snd in
                                Some uu____3748
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3758,FStar_Util.Inl t,uu____3760) ->
                                Some t
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3781,FStar_Util.Inr c,uu____3783) ->
                                Some (FStar_Syntax_Util.comp_result c)
                            | uu____3804 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type ->
                               let head_type =
                                 let uu____3824 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3824 in
                               let uu____3825 =
                                 curried_arrow_formals_comp head_type in
                               (match uu____3825 with
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
                                     | uu____3850 ->
                                         (match (FStar_List.length formals) >
                                                  (FStar_List.length args)
                                          with
                                          | true  ->
                                              encode_partial_app
                                                (Some (formals, c))
                                          | uu____3862 ->
                                              encode_partial_app None)))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3895 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3895 with
            | (bs,body,opening) ->
                let fallback uu____3910 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3915 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3915, [decl]) in
                let is_impure uu___118_3925 =
                  match uu___118_3925 with
                  | FStar_Util.Inl lc ->
                      let uu____3935 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc in
                      Prims.op_Negation uu____3935
                  | FStar_Util.Inr (eff,uu____3937) ->
                      let uu____3943 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3943 Prims.op_Negation in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc ->
                      let uu____3964 =
                        let uu____3965 = lc.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____3965 in
                      FStar_All.pipe_right uu____3964
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar uu____3977 =
                        let uu____3978 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____3978 Prims.fst in
                      (match FStar_Ident.lid_equals eff
                               FStar_Syntax_Const.effect_Tot_lid
                       with
                       | true  ->
                           let uu____3986 =
                             let uu____3987 = new_uvar () in
                             FStar_Syntax_Syntax.mk_Total uu____3987 in
                           FStar_All.pipe_right uu____3986
                             (fun _0_32  -> Some _0_32)
                       | uu____3989 ->
                           (match FStar_Ident.lid_equals eff
                                    FStar_Syntax_Const.effect_GTot_lid
                            with
                            | true  ->
                                let uu____3991 =
                                  let uu____3992 = new_uvar () in
                                  FStar_Syntax_Syntax.mk_GTotal uu____3992 in
                                FStar_All.pipe_right uu____3991
                                  (fun _0_33  -> Some _0_33)
                            | uu____3994 -> None)) in
                (match lopt with
                 | None  ->
                     ((let uu____4003 =
                         let uu____4004 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4004 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4003);
                      fallback ())
                 | Some lc ->
                     let uu____4016 = is_impure lc in
                     (match uu____4016 with
                      | true  -> fallback ()
                      | uu____4019 ->
                          let uu____4020 = encode_binders None bs env in
                          (match uu____4020 with
                           | (vars,guards,envbody,decls,uu____4035) ->
                               let uu____4042 = encode_term body envbody in
                               (match uu____4042 with
                                | (body,decls') ->
                                    let key_body =
                                      let uu____4050 =
                                        let uu____4056 =
                                          let uu____4057 =
                                            let uu____4060 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                guards in
                                            (uu____4060, body) in
                                          FStar_SMTEncoding_Util.mkImp
                                            uu____4057 in
                                        ([], vars, uu____4056) in
                                      FStar_SMTEncoding_Util.mkForall
                                        uu____4050 in
                                    let cvars =
                                      FStar_SMTEncoding_Term.free_variables
                                        key_body in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], cvars, key_body) in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey in
                                    let uu____4071 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____4071 with
                                     | Some (t,uu____4086,uu____4087) ->
                                         let uu____4097 =
                                           let uu____4098 =
                                             let uu____4102 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars in
                                             (t, uu____4102) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4098 in
                                         (uu____4097, [])
                                     | None  ->
                                         let uu____4113 =
                                           is_eta env vars body in
                                         (match uu____4113 with
                                          | Some t -> (t, [])
                                          | None  ->
                                              let cvar_sorts =
                                                FStar_List.map Prims.snd
                                                  cvars in
                                              let fsym =
                                                let uu____4124 =
                                                  let uu____4125 =
                                                    FStar_Util.digest_of_string
                                                      tkey_hash in
                                                  Prims.strcat "Tm_abs_"
                                                    uu____4125 in
                                                varops.mk_unique uu____4124 in
                                              let fdecl =
                                                FStar_SMTEncoding_Term.DeclFun
                                                  (fsym, cvar_sorts,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    None) in
                                              let f =
                                                let uu____4130 =
                                                  let uu____4134 =
                                                    FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV
                                                      cvars in
                                                  (fsym, uu____4134) in
                                                FStar_SMTEncoding_Util.mkApp
                                                  uu____4130 in
                                              let app = mk_Apply f vars in
                                              let typing_f =
                                                let uu____4142 =
                                                  codomain_eff lc in
                                                match uu____4142 with
                                                | None  -> []
                                                | Some c ->
                                                    let tfun =
                                                      FStar_Syntax_Util.arrow
                                                        bs c in
                                                    let uu____4149 =
                                                      encode_term_pred None
                                                        tfun env f in
                                                    (match uu____4149 with
                                                     | (f_has_t,decls'') ->
                                                         let a_name =
                                                           Some
                                                             (Prims.strcat
                                                                "typing_"
                                                                fsym) in
                                                         let uu____4157 =
                                                           let uu____4159 =
                                                             let uu____4160 =
                                                               let uu____4165
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars,
                                                                    f_has_t) in
                                                               (uu____4165,
                                                                 a_name,
                                                                 a_name) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____4160 in
                                                           [uu____4159] in
                                                         FStar_List.append
                                                           decls'' uu____4157) in
                                              let interp_f =
                                                let a_name =
                                                  Some
                                                    (Prims.strcat
                                                       "interpretation_" fsym) in
                                                let uu____4175 =
                                                  let uu____4180 =
                                                    let uu____4181 =
                                                      let uu____4187 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (app, body) in
                                                      ([[app]],
                                                        (FStar_List.append
                                                           vars cvars),
                                                        uu____4187) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____4181 in
                                                  (uu____4180, a_name,
                                                    a_name) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____4175 in
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
           ((uu____4206,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4207;
                          FStar_Syntax_Syntax.lbunivs = uu____4208;
                          FStar_Syntax_Syntax.lbtyp = uu____4209;
                          FStar_Syntax_Syntax.lbeff = uu____4210;
                          FStar_Syntax_Syntax.lbdef = uu____4211;_}::uu____4212),uu____4213)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4231;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4233;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4249 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4262 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4262, [decl_e])))
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
              let uu____4304 = encode_term e1 env in
              match uu____4304 with
              | (ee1,decls1) ->
                  let uu____4311 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4311 with
                   | (xs,e2) ->
                       let uu____4325 = FStar_List.hd xs in
                       (match uu____4325 with
                        | (x,uu____4333) ->
                            let env' = push_term_var env x ee1 in
                            let uu____4335 = encode_body e2 env' in
                            (match uu____4335 with
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
            let uu____4357 =
              let uu____4361 =
                let uu____4362 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4362 in
              gen_term_var env uu____4361 in
            match uu____4357 with
            | (scrsym,scr',env) ->
                let uu____4376 = encode_term e env in
                (match uu____4376 with
                 | (scr,decls) ->
                     let uu____4383 =
                       let encode_branch b uu____4399 =
                         match uu____4399 with
                         | (else_case,decls) ->
                             let uu____4410 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4410 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env p in
                                  FStar_List.fold_right
                                    (fun uu____4440  ->
                                       fun uu____4441  ->
                                         match (uu____4440, uu____4441) with
                                         | ((env0,pattern),(else_case,decls))
                                             ->
                                             let guard = pattern.guard scr' in
                                             let projections =
                                               pattern.projections scr' in
                                             let env =
                                               FStar_All.pipe_right
                                                 projections
                                                 (FStar_List.fold_left
                                                    (fun env  ->
                                                       fun uu____4478  ->
                                                         match uu____4478
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env x t) env) in
                                             let uu____4483 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w ->
                                                   let uu____4498 =
                                                     encode_term w env in
                                                   (match uu____4498 with
                                                    | (w,decls2) ->
                                                        let uu____4506 =
                                                          let uu____4507 =
                                                            let uu____4510 =
                                                              let uu____4511
                                                                =
                                                                let uu____4514
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w,
                                                                  uu____4514) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4511 in
                                                            (guard,
                                                              uu____4510) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4507 in
                                                        (uu____4506, decls2)) in
                                             (match uu____4483 with
                                              | (guard,decls2) ->
                                                  let uu____4522 =
                                                    encode_br br env in
                                                  (match uu____4522 with
                                                   | (br,decls3) ->
                                                       let uu____4530 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard, br,
                                                             else_case) in
                                                       (uu____4530,
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls2 decls3))))))
                                    patterns (else_case, decls)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4383 with
                      | (match_tm,decls) ->
                          let uu____4542 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4542, decls)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4573 -> let uu____4574 = encode_one_pat env pat in [uu____4574]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4586 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       match uu____4586 with
       | true  ->
           let uu____4587 = FStar_Syntax_Print.pat_to_string pat in
           FStar_Util.print1 "Encoding pattern %s\n" uu____4587
       | uu____4588 -> ());
      (let uu____4589 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4589 with
       | (vars,pat_term) ->
           let uu____4599 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4622  ->
                     fun v  ->
                       match uu____4622 with
                       | (env,vars) ->
                           let uu____4650 = gen_term_var env v in
                           (match uu____4650 with
                            | (xx,uu____4662,env) ->
                                (env,
                                  ((v,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars)))) (env, [])) in
           (match uu____4599 with
            | (env,vars) ->
                let rec mk_guard pat scrutinee =
                  match pat.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4709 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4717 =
                        let uu____4720 = encode_const c in
                        (scrutinee, uu____4720) in
                      FStar_SMTEncoding_Util.mkEq uu____4717
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4739 =
                          FStar_TypeChecker_Env.datacons_of_typ env.tcenv
                            tc_name in
                        match uu____4739 with
                        | (uu____4743,uu____4744::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4746 ->
                            mk_data_tester env
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4767  ->
                                  match uu____4767 with
                                  | (arg,uu____4773) ->
                                      let proj =
                                        primitive_projector_by_pos env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4783 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4783)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat scrutinee =
                  match pat.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4802 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4817 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4832 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4854  ->
                                  match uu____4854 with
                                  | (arg,uu____4863) ->
                                      let proj =
                                        primitive_projector_by_pos env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4873 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____4873)) in
                      FStar_All.pipe_right uu____4832 FStar_List.flatten in
                let pat_term uu____4889 = encode_term pat_term env in
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
      let uu____4896 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____4911  ->
                fun uu____4912  ->
                  match (uu____4911, uu____4912) with
                  | ((tms,decls),(t,uu____4932)) ->
                      let uu____4943 = encode_term t env in
                      (match uu____4943 with
                       | (t,decls') ->
                           ((t :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____4896 with | (l,decls) -> ((FStar_List.rev l), decls)
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
            let uu____4981 = FStar_Syntax_Util.list_elements e in
            match uu____4981 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 []) in
          let one_pat p =
            let uu____4999 =
              let uu____5009 = FStar_Syntax_Util.unmeta p in
              FStar_All.pipe_right uu____5009 FStar_Syntax_Util.head_and_args in
            match uu____4999 with
            | (head,args) ->
                let uu____5040 =
                  let uu____5048 =
                    let uu____5049 = FStar_Syntax_Util.un_uinst head in
                    uu____5049.FStar_Syntax_Syntax.n in
                  (uu____5048, args) in
                (match uu____5040 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5063,uu____5064)::(e,uu____5066)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5097)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5118 -> failwith "Unexpected pattern term") in
          let lemma_pats p =
            let elts = list_elements p in
            let smt_pat_or t =
              let uu____5151 =
                let uu____5161 = FStar_Syntax_Util.unmeta t in
                FStar_All.pipe_right uu____5161
                  FStar_Syntax_Util.head_and_args in
              match uu____5151 with
              | (head,args) ->
                  let uu____5190 =
                    let uu____5198 =
                      let uu____5199 = FStar_Syntax_Util.un_uinst head in
                      uu____5199.FStar_Syntax_Syntax.n in
                    (uu____5198, args) in
                  (match uu____5190 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5212)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5232 -> None) in
            match elts with
            | t::[] ->
                let uu____5250 = smt_pat_or t in
                (match uu____5250 with
                 | Some e ->
                     let uu____5266 = list_elements e in
                     FStar_All.pipe_right uu____5266
                       (FStar_List.map
                          (fun branch  ->
                             let uu____5283 = list_elements branch in
                             FStar_All.pipe_right uu____5283
                               (FStar_List.map one_pat)))
                 | uu____5297 ->
                     let uu____5301 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat) in
                     [uu____5301])
            | uu____5332 ->
                let uu____5334 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat) in
                [uu____5334] in
          let uu____5365 =
            let uu____5381 =
              let uu____5382 = FStar_Syntax_Subst.compress t in
              uu____5382.FStar_Syntax_Syntax.n in
            match uu____5381 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5412 = FStar_Syntax_Subst.open_comp binders c in
                (match uu____5412 with
                 | (binders,c) ->
                     (match c.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5447;
                            FStar_Syntax_Syntax.effect_name = uu____5448;
                            FStar_Syntax_Syntax.result_typ = uu____5449;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5451)::(post,uu____5453)::(pats,uu____5455)::[];
                            FStar_Syntax_Syntax.flags = uu____5456;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats in
                          let uu____5490 = lemma_pats pats' in
                          (binders, pre, post, uu____5490)
                      | uu____5509 -> failwith "impos"))
            | uu____5525 -> failwith "Impos" in
          match uu____5365 with
          | (binders,pre,post,patterns) ->
              let uu____5569 = encode_binders None binders env in
              (match uu____5569 with
               | (vars,guards,env,decls,uu____5584) ->
                   let uu____5591 =
                     let uu____5598 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch  ->
                               let uu____5629 =
                                 let uu____5634 =
                                   FStar_All.pipe_right branch
                                     (FStar_List.map
                                        (fun uu____5650  ->
                                           match uu____5650 with
                                           | (t,uu____5657) ->
                                               encode_term t
                                                 (let uu___144_5660 = env in
                                                  {
                                                    bindings =
                                                      (uu___144_5660.bindings);
                                                    depth =
                                                      (uu___144_5660.depth);
                                                    tcenv =
                                                      (uu___144_5660.tcenv);
                                                    warn =
                                                      (uu___144_5660.warn);
                                                    cache =
                                                      (uu___144_5660.cache);
                                                    nolabels =
                                                      (uu___144_5660.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___144_5660.encode_non_total_function_typ)
                                                  }))) in
                                 FStar_All.pipe_right uu____5634
                                   FStar_List.unzip in
                               match uu____5629 with
                               | (pats,decls) -> (pats, decls))) in
                     FStar_All.pipe_right uu____5598 FStar_List.unzip in
                   (match uu____5591 with
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
                                           let uu____5724 =
                                             let uu____5725 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5725 e in
                                           uu____5724 :: p))
                               | uu____5726 ->
                                   let rec aux tl vars =
                                     match vars with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5755 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl e in
                                                 uu____5755 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars
                                         ->
                                         let uu____5763 =
                                           let uu____5764 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort) in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5764 tl in
                                         aux uu____5763 vars
                                     | uu____5765 -> pats in
                                   let uu____5769 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort) in
                                   aux uu____5769 vars) in
                        let env =
                          let uu___145_5771 = env in
                          {
                            bindings = (uu___145_5771.bindings);
                            depth = (uu___145_5771.depth);
                            tcenv = (uu___145_5771.tcenv);
                            warn = (uu___145_5771.warn);
                            cache = (uu___145_5771.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___145_5771.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___145_5771.encode_non_total_function_typ)
                          } in
                        let uu____5772 =
                          let uu____5775 = FStar_Syntax_Util.unmeta pre in
                          encode_formula uu____5775 env in
                        (match uu____5772 with
                         | (pre,decls'') ->
                             let uu____5780 =
                               let uu____5783 = FStar_Syntax_Util.unmeta post in
                               encode_formula uu____5783 env in
                             (match uu____5780 with
                              | (post,decls''') ->
                                  let decls =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls')
                                         (FStar_List.append decls'' decls''')) in
                                  let uu____5790 =
                                    let uu____5791 =
                                      let uu____5797 =
                                        let uu____5798 =
                                          let uu____5801 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre :: guards) in
                                          (uu____5801, post) in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5798 in
                                      (pats, vars, uu____5797) in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5791 in
                                  (uu____5790, decls)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug phi =
        let uu____5814 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        match uu____5814 with
        | true  ->
            let uu____5815 = FStar_Syntax_Print.tag_of_term phi in
            let uu____5816 = FStar_Syntax_Print.term_to_string phi in
            FStar_Util.print2 "Formula (%s)  %s\n" uu____5815 uu____5816
        | uu____5817 -> () in
      let enc f r l =
        let uu____5843 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5856 = encode_term (Prims.fst x) env in
                 match uu____5856 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5843 with
        | (decls,args) ->
            let uu____5873 =
              let uu___146_5874 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___146_5874.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___146_5874.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5873, decls) in
      let const_op f r uu____5893 = let uu____5896 = f r in (uu____5896, []) in
      let un_op f l =
        let uu____5912 = FStar_List.hd l in FStar_All.pipe_left f uu____5912 in
      let bin_op f uu___119_5925 =
        match uu___119_5925 with
        | t1::t2::[] -> f (t1, t2)
        | uu____5933 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____5960 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____5969  ->
                 match uu____5969 with
                 | (t,uu____5977) ->
                     let uu____5978 = encode_formula t env in
                     (match uu____5978 with
                      | (phi,decls') ->
                          ((FStar_List.append decls decls'), phi))) [] l in
        match uu____5960 with
        | (decls,phis) ->
            let uu____5995 =
              let uu___147_5996 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___147_5996.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___147_5996.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5995, decls) in
      let eq_op r uu___120_6012 =
        match uu___120_6012 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6072 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6072 r [e1; e2]
        | l ->
            let uu____6092 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6092 r l in
      let mk_imp r uu___121_6111 =
        match uu___121_6111 with
        | (lhs,uu____6115)::(rhs,uu____6117)::[] ->
            let uu____6138 = encode_formula rhs env in
            (match uu____6138 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6147) ->
                      (l1, decls1)
                  | uu____6150 ->
                      let uu____6151 = encode_formula lhs env in
                      (match uu____6151 with
                       | (l2,decls2) ->
                           let uu____6158 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6158, (FStar_List.append decls1 decls2)))))
        | uu____6160 -> failwith "impossible" in
      let mk_ite r uu___122_6175 =
        match uu___122_6175 with
        | (guard,uu____6179)::(_then,uu____6181)::(_else,uu____6183)::[] ->
            let uu____6212 = encode_formula guard env in
            (match uu____6212 with
             | (g,decls1) ->
                 let uu____6219 = encode_formula _then env in
                 (match uu____6219 with
                  | (t,decls2) ->
                      let uu____6226 = encode_formula _else env in
                      (match uu____6226 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6235 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6254 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6254 in
      let connectives =
        let uu____6266 =
          let uu____6275 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6275) in
        let uu____6288 =
          let uu____6298 =
            let uu____6307 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6307) in
          let uu____6320 =
            let uu____6330 =
              let uu____6340 =
                let uu____6349 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6349) in
              let uu____6362 =
                let uu____6372 =
                  let uu____6382 =
                    let uu____6391 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6391) in
                  [uu____6382;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6372 in
              uu____6340 :: uu____6362 in
            (FStar_Syntax_Const.imp_lid, mk_imp) :: uu____6330 in
          uu____6298 :: uu____6320 in
        uu____6266 :: uu____6288 in
      let rec fallback phi =
        match phi.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6553 = encode_formula phi' env in
            (match uu____6553 with
             | (phi,decls) ->
                 let uu____6560 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi, msg, r)) r in
                 (uu____6560, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6561 ->
            let uu____6566 = FStar_Syntax_Util.unmeta phi in
            encode_formula uu____6566 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6595 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6595 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6603;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6605;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6621 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6621 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head,args) ->
            let head = FStar_Syntax_Util.un_uinst head in
            (match ((head.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6653::(x,uu____6655)::(t,uu____6657)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6691 = encode_term x env in
                 (match uu____6691 with
                  | (x,decls) ->
                      let uu____6698 = encode_term t env in
                      (match uu____6698 with
                       | (t,decls') ->
                           let uu____6705 =
                             FStar_SMTEncoding_Term.mk_HasType x t in
                           (uu____6705, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6709)::(msg,uu____6711)::(phi,uu____6713)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6747 =
                   let uu____6750 =
                     let uu____6751 = FStar_Syntax_Subst.compress r in
                     uu____6751.FStar_Syntax_Syntax.n in
                   let uu____6754 =
                     let uu____6755 = FStar_Syntax_Subst.compress msg in
                     uu____6755.FStar_Syntax_Syntax.n in
                   (uu____6750, uu____6754) in
                 (match uu____6747 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6762))) ->
                      let phi =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r,
                                     false))))) None r in
                      fallback phi
                  | uu____6778 -> fallback phi)
             | uu____6781 when head_redex env head ->
                 let uu____6789 = whnf env phi in
                 encode_formula uu____6789 env
             | uu____6790 ->
                 let uu____6798 = encode_term phi env in
                 (match uu____6798 with
                  | (tt,decls) ->
                      let uu____6805 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___148_6806 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___148_6806.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___148_6806.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6805, decls)))
        | uu____6809 ->
            let uu____6810 = encode_term phi env in
            (match uu____6810 with
             | (tt,decls) ->
                 let uu____6817 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___149_6818 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___149_6818.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___149_6818.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6817, decls)) in
      let encode_q_body env bs ps body =
        let uu____6845 = encode_binders None bs env in
        match uu____6845 with
        | (vars,guards,env,decls,uu____6867) ->
            let uu____6874 =
              let uu____6881 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____6904 =
                          let uu____6909 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____6923  ->
                                    match uu____6923 with
                                    | (t,uu____6929) ->
                                        encode_term t
                                          (let uu___150_6930 = env in
                                           {
                                             bindings =
                                               (uu___150_6930.bindings);
                                             depth = (uu___150_6930.depth);
                                             tcenv = (uu___150_6930.tcenv);
                                             warn = (uu___150_6930.warn);
                                             cache = (uu___150_6930.cache);
                                             nolabels =
                                               (uu___150_6930.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___150_6930.encode_non_total_function_typ)
                                           }))) in
                          FStar_All.pipe_right uu____6909 FStar_List.unzip in
                        match uu____6904 with
                        | (p,decls) -> (p, (FStar_List.flatten decls)))) in
              FStar_All.pipe_right uu____6881 FStar_List.unzip in
            (match uu____6874 with
             | (pats,decls') ->
                 let uu____6982 = encode_formula body env in
                 (match uu____6982 with
                  | (body,decls'') ->
                      let guards =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7001;
                             FStar_SMTEncoding_Term.rng = uu____7002;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7010 -> guards in
                      let uu____7013 = FStar_SMTEncoding_Util.mk_and_l guards in
                      (vars, pats, uu____7013, body,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug phi;
      (let phi = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7047  ->
                   match uu____7047 with
                   | (x,uu____7051) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats with
         | [] -> ()
         | hd::tl ->
             let pat_vars =
               let uu____7057 = FStar_Syntax_Free.names hd in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7063 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7063) uu____7057 tl in
             let uu____7065 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7077  ->
                       match uu____7077 with
                       | (b,uu____7081) ->
                           let uu____7082 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7082)) in
             (match uu____7065 with
              | None  -> ()
              | Some (x,uu____7086) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd.FStar_Syntax_Syntax.pos tl in
                  let uu____7096 =
                    let uu____7097 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7097 in
                  FStar_Errors.warn pos uu____7096) in
       let uu____7098 = FStar_Syntax_Util.destruct_typ_as_formula phi in
       match uu____7098 with
       | None  -> fallback phi
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7104 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7140  ->
                     match uu____7140 with
                     | (l,uu____7150) -> FStar_Ident.lid_equals op l)) in
           (match uu____7104 with
            | None  -> fallback phi
            | Some (uu____7173,f) -> f phi.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7202 = encode_q_body env vars pats body in
             match uu____7202 with
             | (vars,pats,guard,body,decls) ->
                 let tm =
                   let uu____7228 =
                     let uu____7234 =
                       FStar_SMTEncoding_Util.mkImp (guard, body) in
                     (pats, vars, uu____7234) in
                   FStar_SMTEncoding_Term.mkForall uu____7228
                     phi.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7246 = encode_q_body env vars pats body in
             match uu____7246 with
             | (vars,pats,guard,body,decls) ->
                 let uu____7271 =
                   let uu____7272 =
                     let uu____7278 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body) in
                     (pats, vars, uu____7278) in
                   FStar_SMTEncoding_Term.mkExists uu____7272
                     phi.FStar_Syntax_Syntax.pos in
                 (uu____7271, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7327 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7327 with
  | (asym,a) ->
      let uu____7332 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7332 with
       | (xsym,x) ->
           let uu____7337 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7337 with
            | (ysym,y) ->
                let quant vars body x =
                  let xname_decl =
                    let uu____7367 =
                      let uu____7373 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x, uu____7373, FStar_SMTEncoding_Term.Term_sort, None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7367 in
                  let xtok = Prims.strcat x "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7388 =
                      let uu____7392 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x, uu____7392) in
                    FStar_SMTEncoding_Util.mkApp uu____7388 in
                  let xtok = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok vars in
                  let uu____7400 =
                    let uu____7402 =
                      let uu____7404 =
                        let uu____7406 =
                          let uu____7407 =
                            let uu____7412 =
                              let uu____7413 =
                                let uu____7419 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7419) in
                              FStar_SMTEncoding_Util.mkForall uu____7413 in
                            (uu____7412, None,
                              (Some (Prims.strcat "primitive_" x))) in
                          FStar_SMTEncoding_Term.Assume uu____7407 in
                        let uu____7429 =
                          let uu____7431 =
                            let uu____7432 =
                              let uu____7437 =
                                let uu____7438 =
                                  let uu____7444 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7444) in
                                FStar_SMTEncoding_Util.mkForall uu____7438 in
                              (uu____7437,
                                (Some "Name-token correspondence"),
                                (Some
                                   (Prims.strcat "token_correspondence_" x))) in
                            FStar_SMTEncoding_Term.Assume uu____7432 in
                          [uu____7431] in
                        uu____7406 :: uu____7429 in
                      xtok_decl :: uu____7404 in
                    xname_decl :: uu____7402 in
                  (xtok, uu____7400) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims =
                  let uu____7494 =
                    let uu____7502 =
                      let uu____7508 =
                        let uu____7509 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7509 in
                      quant axy uu____7508 in
                    (FStar_Syntax_Const.op_Eq, uu____7502) in
                  let uu____7515 =
                    let uu____7524 =
                      let uu____7532 =
                        let uu____7538 =
                          let uu____7539 =
                            let uu____7540 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7540 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7539 in
                        quant axy uu____7538 in
                      (FStar_Syntax_Const.op_notEq, uu____7532) in
                    let uu____7546 =
                      let uu____7555 =
                        let uu____7563 =
                          let uu____7569 =
                            let uu____7570 =
                              let uu____7571 =
                                let uu____7574 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7575 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7574, uu____7575) in
                              FStar_SMTEncoding_Util.mkLT uu____7571 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7570 in
                          quant xy uu____7569 in
                        (FStar_Syntax_Const.op_LT, uu____7563) in
                      let uu____7581 =
                        let uu____7590 =
                          let uu____7598 =
                            let uu____7604 =
                              let uu____7605 =
                                let uu____7606 =
                                  let uu____7609 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7610 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7609, uu____7610) in
                                FStar_SMTEncoding_Util.mkLTE uu____7606 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7605 in
                            quant xy uu____7604 in
                          (FStar_Syntax_Const.op_LTE, uu____7598) in
                        let uu____7616 =
                          let uu____7625 =
                            let uu____7633 =
                              let uu____7639 =
                                let uu____7640 =
                                  let uu____7641 =
                                    let uu____7644 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7645 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7644, uu____7645) in
                                  FStar_SMTEncoding_Util.mkGT uu____7641 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7640 in
                              quant xy uu____7639 in
                            (FStar_Syntax_Const.op_GT, uu____7633) in
                          let uu____7651 =
                            let uu____7660 =
                              let uu____7668 =
                                let uu____7674 =
                                  let uu____7675 =
                                    let uu____7676 =
                                      let uu____7679 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7680 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7679, uu____7680) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7676 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7675 in
                                quant xy uu____7674 in
                              (FStar_Syntax_Const.op_GTE, uu____7668) in
                            let uu____7686 =
                              let uu____7695 =
                                let uu____7703 =
                                  let uu____7709 =
                                    let uu____7710 =
                                      let uu____7711 =
                                        let uu____7714 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7715 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7714, uu____7715) in
                                      FStar_SMTEncoding_Util.mkSub uu____7711 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7710 in
                                  quant xy uu____7709 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7703) in
                              let uu____7721 =
                                let uu____7730 =
                                  let uu____7738 =
                                    let uu____7744 =
                                      let uu____7745 =
                                        let uu____7746 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7746 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7745 in
                                    quant qx uu____7744 in
                                  (FStar_Syntax_Const.op_Minus, uu____7738) in
                                let uu____7752 =
                                  let uu____7761 =
                                    let uu____7769 =
                                      let uu____7775 =
                                        let uu____7776 =
                                          let uu____7777 =
                                            let uu____7780 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7781 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7780, uu____7781) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7777 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7776 in
                                      quant xy uu____7775 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7769) in
                                  let uu____7787 =
                                    let uu____7796 =
                                      let uu____7804 =
                                        let uu____7810 =
                                          let uu____7811 =
                                            let uu____7812 =
                                              let uu____7815 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7816 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7815, uu____7816) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7812 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7811 in
                                        quant xy uu____7810 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7804) in
                                    let uu____7822 =
                                      let uu____7831 =
                                        let uu____7839 =
                                          let uu____7845 =
                                            let uu____7846 =
                                              let uu____7847 =
                                                let uu____7850 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7851 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7850, uu____7851) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7847 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7846 in
                                          quant xy uu____7845 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7839) in
                                      let uu____7857 =
                                        let uu____7866 =
                                          let uu____7874 =
                                            let uu____7880 =
                                              let uu____7881 =
                                                let uu____7882 =
                                                  let uu____7885 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____7886 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____7885, uu____7886) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____7882 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____7881 in
                                            quant xy uu____7880 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____7874) in
                                        let uu____7892 =
                                          let uu____7901 =
                                            let uu____7909 =
                                              let uu____7915 =
                                                let uu____7916 =
                                                  let uu____7917 =
                                                    let uu____7920 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____7921 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____7920, uu____7921) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____7917 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____7916 in
                                              quant xy uu____7915 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____7909) in
                                          let uu____7927 =
                                            let uu____7936 =
                                              let uu____7944 =
                                                let uu____7950 =
                                                  let uu____7951 =
                                                    let uu____7952 =
                                                      let uu____7955 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____7956 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____7955,
                                                        uu____7956) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____7952 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____7951 in
                                                quant xy uu____7950 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____7944) in
                                            let uu____7962 =
                                              let uu____7971 =
                                                let uu____7979 =
                                                  let uu____7985 =
                                                    let uu____7986 =
                                                      let uu____7987 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____7987 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____7986 in
                                                  quant qx uu____7985 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____7979) in
                                              [uu____7971] in
                                            uu____7936 :: uu____7962 in
                                          uu____7901 :: uu____7927 in
                                        uu____7866 :: uu____7892 in
                                      uu____7831 :: uu____7857 in
                                    uu____7796 :: uu____7822 in
                                  uu____7761 :: uu____7787 in
                                uu____7730 :: uu____7752 in
                              uu____7695 :: uu____7721 in
                            uu____7660 :: uu____7686 in
                          uu____7625 :: uu____7651 in
                        uu____7590 :: uu____7616 in
                      uu____7555 :: uu____7581 in
                    uu____7524 :: uu____7546 in
                  uu____7494 :: uu____7515 in
                let mk l v =
                  let uu____8115 =
                    let uu____8120 =
                      FStar_All.pipe_right prims
                        (FStar_List.find
                           (fun uu____8152  ->
                              match uu____8152 with
                              | (l',uu____8161) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8120
                      (FStar_Option.map
                         (fun uu____8194  ->
                            match uu____8194 with | (uu____8205,b) -> b v)) in
                  FStar_All.pipe_right uu____8115 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims
                    (FStar_Util.for_some
                       (fun uu____8246  ->
                          match uu____8246 with
                          | (l',uu____8255) -> FStar_Ident.lid_equals l l')) in
                { mk; is }))
let pretype_axiom:
  FStar_SMTEncoding_Term.term ->
    (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.decl
  =
  fun tapp  ->
    fun vars  ->
      let uu____8278 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      match uu____8278 with
      | (xxsym,xx) ->
          let uu____8283 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
          (match uu____8283 with
           | (ffsym,ff) ->
               let xx_has_type =
                 FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
               let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
               let uu____8290 =
                 let uu____8295 =
                   let uu____8296 =
                     let uu____8302 =
                       let uu____8303 =
                         let uu____8306 =
                           let uu____8307 =
                             let uu____8310 =
                               FStar_SMTEncoding_Util.mkApp ("PreType", [xx]) in
                             (tapp, uu____8310) in
                           FStar_SMTEncoding_Util.mkEq uu____8307 in
                         (xx_has_type, uu____8306) in
                       FStar_SMTEncoding_Util.mkImp uu____8303 in
                     ([[xx_has_type]],
                       ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                       (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                       uu____8302) in
                   FStar_SMTEncoding_Util.mkForall uu____8296 in
                 let uu____8323 =
                   let uu____8325 =
                     let uu____8326 =
                       let uu____8327 = FStar_Util.digest_of_string tapp_hash in
                       Prims.strcat "pretyping_" uu____8327 in
                     varops.mk_unique uu____8326 in
                   Some uu____8325 in
                 (uu____8295, (Some "pretyping"), uu____8323) in
               FStar_SMTEncoding_Term.Assume uu____8290)
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
    let uu____8358 =
      let uu____8359 =
        let uu____8364 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8364, (Some "unit typing"), (Some "unit_typing")) in
      FStar_SMTEncoding_Term.Assume uu____8359 in
    let uu____8367 =
      let uu____8369 =
        let uu____8370 =
          let uu____8375 =
            let uu____8376 =
              let uu____8382 =
                let uu____8383 =
                  let uu____8386 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8386) in
                FStar_SMTEncoding_Util.mkImp uu____8383 in
              ([[typing_pred]], [xx], uu____8382) in
            mkForall_fuel uu____8376 in
          (uu____8375, (Some "unit inversion"), (Some "unit_inversion")) in
        FStar_SMTEncoding_Term.Assume uu____8370 in
      [uu____8369] in
    uu____8358 :: uu____8367 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8415 =
      let uu____8416 =
        let uu____8421 =
          let uu____8422 =
            let uu____8428 =
              let uu____8431 =
                let uu____8433 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8433] in
              [uu____8431] in
            let uu____8436 =
              let uu____8437 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8437 tt in
            (uu____8428, [bb], uu____8436) in
          FStar_SMTEncoding_Util.mkForall uu____8422 in
        (uu____8421, (Some "bool typing"), (Some "bool_typing")) in
      FStar_SMTEncoding_Term.Assume uu____8416 in
    let uu____8449 =
      let uu____8451 =
        let uu____8452 =
          let uu____8457 =
            let uu____8458 =
              let uu____8464 =
                let uu____8465 =
                  let uu____8468 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8468) in
                FStar_SMTEncoding_Util.mkImp uu____8465 in
              ([[typing_pred]], [xx], uu____8464) in
            mkForall_fuel uu____8458 in
          (uu____8457, (Some "bool inversion"), (Some "bool_inversion")) in
        FStar_SMTEncoding_Term.Assume uu____8452 in
      [uu____8451] in
    uu____8415 :: uu____8449 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8503 =
        let uu____8504 =
          let uu____8508 =
            let uu____8510 =
              let uu____8512 =
                let uu____8514 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8515 =
                  let uu____8517 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8517] in
                uu____8514 :: uu____8515 in
              tt :: uu____8512 in
            tt :: uu____8510 in
          ("Prims.Precedes", uu____8508) in
        FStar_SMTEncoding_Util.mkApp uu____8504 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8503 in
    let precedes_y_x =
      let uu____8520 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8520 in
    let uu____8522 =
      let uu____8523 =
        let uu____8528 =
          let uu____8529 =
            let uu____8535 =
              let uu____8538 =
                let uu____8540 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8540] in
              [uu____8538] in
            let uu____8543 =
              let uu____8544 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8544 tt in
            (uu____8535, [bb], uu____8543) in
          FStar_SMTEncoding_Util.mkForall uu____8529 in
        (uu____8528, (Some "int typing"), (Some "int_typing")) in
      FStar_SMTEncoding_Term.Assume uu____8523 in
    let uu____8556 =
      let uu____8558 =
        let uu____8559 =
          let uu____8564 =
            let uu____8565 =
              let uu____8571 =
                let uu____8572 =
                  let uu____8575 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8575) in
                FStar_SMTEncoding_Util.mkImp uu____8572 in
              ([[typing_pred]], [xx], uu____8571) in
            mkForall_fuel uu____8565 in
          (uu____8564, (Some "int inversion"), (Some "int_inversion")) in
        FStar_SMTEncoding_Term.Assume uu____8559 in
      let uu____8589 =
        let uu____8591 =
          let uu____8592 =
            let uu____8597 =
              let uu____8598 =
                let uu____8604 =
                  let uu____8605 =
                    let uu____8608 =
                      let uu____8609 =
                        let uu____8611 =
                          let uu____8613 =
                            let uu____8615 =
                              let uu____8616 =
                                let uu____8619 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8620 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8619, uu____8620) in
                              FStar_SMTEncoding_Util.mkGT uu____8616 in
                            let uu____8621 =
                              let uu____8623 =
                                let uu____8624 =
                                  let uu____8627 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8628 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8627, uu____8628) in
                                FStar_SMTEncoding_Util.mkGTE uu____8624 in
                              let uu____8629 =
                                let uu____8631 =
                                  let uu____8632 =
                                    let uu____8635 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8636 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8635, uu____8636) in
                                  FStar_SMTEncoding_Util.mkLT uu____8632 in
                                [uu____8631] in
                              uu____8623 :: uu____8629 in
                            uu____8615 :: uu____8621 in
                          typing_pred_y :: uu____8613 in
                        typing_pred :: uu____8611 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8609 in
                    (uu____8608, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8605 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8604) in
              mkForall_fuel uu____8598 in
            (uu____8597, (Some "well-founded ordering on nat (alt)"),
              (Some "well-founded-ordering-on-nat")) in
          FStar_SMTEncoding_Term.Assume uu____8592 in
        [uu____8591] in
      uu____8558 :: uu____8589 in
    uu____8522 :: uu____8556 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8667 =
      let uu____8668 =
        let uu____8673 =
          let uu____8674 =
            let uu____8680 =
              let uu____8683 =
                let uu____8685 = FStar_SMTEncoding_Term.boxString b in
                [uu____8685] in
              [uu____8683] in
            let uu____8688 =
              let uu____8689 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8689 tt in
            (uu____8680, [bb], uu____8688) in
          FStar_SMTEncoding_Util.mkForall uu____8674 in
        (uu____8673, (Some "string typing"), (Some "string_typing")) in
      FStar_SMTEncoding_Term.Assume uu____8668 in
    let uu____8701 =
      let uu____8703 =
        let uu____8704 =
          let uu____8709 =
            let uu____8710 =
              let uu____8716 =
                let uu____8717 =
                  let uu____8720 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8720) in
                FStar_SMTEncoding_Util.mkImp uu____8717 in
              ([[typing_pred]], [xx], uu____8716) in
            mkForall_fuel uu____8710 in
          (uu____8709, (Some "string inversion"), (Some "string_inversion")) in
        FStar_SMTEncoding_Term.Assume uu____8704 in
      [uu____8703] in
    uu____8667 :: uu____8701 in
  let mk_ref env reft_name uu____8743 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8754 =
        let uu____8758 =
          let uu____8760 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8760] in
        (reft_name, uu____8758) in
      FStar_SMTEncoding_Util.mkApp uu____8754 in
    let refb =
      let uu____8763 =
        let uu____8767 =
          let uu____8769 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8769] in
        (reft_name, uu____8767) in
      FStar_SMTEncoding_Util.mkApp uu____8763 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8773 =
      let uu____8774 =
        let uu____8779 =
          let uu____8780 =
            let uu____8786 =
              let uu____8787 =
                let uu____8790 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8790) in
              FStar_SMTEncoding_Util.mkImp uu____8787 in
            ([[typing_pred]], [xx; aa], uu____8786) in
          mkForall_fuel uu____8780 in
        (uu____8779, (Some "ref inversion"), (Some "ref_inversion")) in
      FStar_SMTEncoding_Term.Assume uu____8774 in
    let uu____8806 =
      let uu____8808 =
        let uu____8809 =
          let uu____8814 =
            let uu____8815 =
              let uu____8821 =
                let uu____8822 =
                  let uu____8825 =
                    FStar_SMTEncoding_Util.mkAnd (typing_pred, typing_pred_b) in
                  let uu____8826 =
                    let uu____8827 =
                      let uu____8830 = FStar_SMTEncoding_Util.mkFreeV aa in
                      let uu____8831 = FStar_SMTEncoding_Util.mkFreeV bb in
                      (uu____8830, uu____8831) in
                    FStar_SMTEncoding_Util.mkEq uu____8827 in
                  (uu____8825, uu____8826) in
                FStar_SMTEncoding_Util.mkImp uu____8822 in
              ([[typing_pred; typing_pred_b]], [xx; aa; bb], uu____8821) in
            mkForall_fuel' (Prims.parse_int "2") uu____8815 in
          (uu____8814, (Some "ref typing is injective"),
            (Some "ref_injectivity")) in
        FStar_SMTEncoding_Term.Assume uu____8809 in
      [uu____8808] in
    uu____8773 :: uu____8806 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), (Some "true_interp"))] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8875 =
      let uu____8876 =
        let uu____8881 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8881, (Some "False interpretation"), (Some "false_interp")) in
      FStar_SMTEncoding_Term.Assume uu____8876 in
    [uu____8875] in
  let mk_and_interp env conj uu____8893 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____8903 =
        let uu____8907 =
          let uu____8909 = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
          [uu____8909] in
        ("Valid", uu____8907) in
      FStar_SMTEncoding_Util.mkApp uu____8903 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8916 =
      let uu____8917 =
        let uu____8922 =
          let uu____8923 =
            let uu____8929 =
              let uu____8930 =
                let uu____8933 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____8933, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8930 in
            ([[valid]], [aa; bb], uu____8929) in
          FStar_SMTEncoding_Util.mkForall uu____8923 in
        (uu____8922, (Some "/\\ interpretation"), (Some "l_and-interp")) in
      FStar_SMTEncoding_Term.Assume uu____8917 in
    [uu____8916] in
  let mk_or_interp env disj uu____8958 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____8968 =
        let uu____8972 =
          let uu____8974 = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
          [uu____8974] in
        ("Valid", uu____8972) in
      FStar_SMTEncoding_Util.mkApp uu____8968 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8981 =
      let uu____8982 =
        let uu____8987 =
          let uu____8988 =
            let uu____8994 =
              let uu____8995 =
                let uu____8998 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____8998, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8995 in
            ([[valid]], [aa; bb], uu____8994) in
          FStar_SMTEncoding_Util.mkForall uu____8988 in
        (uu____8987, (Some "\\/ interpretation"), (Some "l_or-interp")) in
      FStar_SMTEncoding_Term.Assume uu____8982 in
    [uu____8981] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x = FStar_SMTEncoding_Util.mkFreeV xx in
    let y = FStar_SMTEncoding_Util.mkFreeV yy in
    let valid =
      let uu____9037 =
        let uu____9041 =
          let uu____9043 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x; y]) in
          [uu____9043] in
        ("Valid", uu____9041) in
      FStar_SMTEncoding_Util.mkApp uu____9037 in
    let uu____9046 =
      let uu____9047 =
        let uu____9052 =
          let uu____9053 =
            let uu____9059 =
              let uu____9060 =
                let uu____9063 = FStar_SMTEncoding_Util.mkEq (x, y) in
                (uu____9063, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9060 in
            ([[valid]], [aa; xx; yy], uu____9059) in
          FStar_SMTEncoding_Util.mkForall uu____9053 in
        (uu____9052, (Some "Eq2 interpretation"), (Some "eq2-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9047 in
    [uu____9046] in
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
      let uu____9108 =
        let uu____9112 =
          let uu____9114 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x; y]) in
          [uu____9114] in
        ("Valid", uu____9112) in
      FStar_SMTEncoding_Util.mkApp uu____9108 in
    let uu____9117 =
      let uu____9118 =
        let uu____9123 =
          let uu____9124 =
            let uu____9130 =
              let uu____9131 =
                let uu____9134 = FStar_SMTEncoding_Util.mkEq (x, y) in
                (uu____9134, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9131 in
            ([[valid]], [aa; bb; xx; yy], uu____9130) in
          FStar_SMTEncoding_Util.mkForall uu____9124 in
        (uu____9123, (Some "Eq3 interpretation"), (Some "eq3-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9118 in
    [uu____9117] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9173 =
        let uu____9177 =
          let uu____9179 = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
          [uu____9179] in
        ("Valid", uu____9177) in
      FStar_SMTEncoding_Util.mkApp uu____9173 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9186 =
      let uu____9187 =
        let uu____9192 =
          let uu____9193 =
            let uu____9199 =
              let uu____9200 =
                let uu____9203 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9203, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9200 in
            ([[valid]], [aa; bb], uu____9199) in
          FStar_SMTEncoding_Util.mkForall uu____9193 in
        (uu____9192, (Some "==> interpretation"), (Some "l_imp-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9187 in
    [uu____9186] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9238 =
        let uu____9242 =
          let uu____9244 = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
          [uu____9244] in
        ("Valid", uu____9242) in
      FStar_SMTEncoding_Util.mkApp uu____9238 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9251 =
      let uu____9252 =
        let uu____9257 =
          let uu____9258 =
            let uu____9264 =
              let uu____9265 =
                let uu____9268 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9268, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9265 in
            ([[valid]], [aa; bb], uu____9264) in
          FStar_SMTEncoding_Util.mkForall uu____9258 in
        (uu____9257, (Some "<==> interpretation"), (Some "l_iff-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9252 in
    [uu____9251] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let valid =
      let uu____9299 =
        let uu____9303 =
          let uu____9305 = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
          [uu____9305] in
        ("Valid", uu____9303) in
      FStar_SMTEncoding_Util.mkApp uu____9299 in
    let not_valid_a =
      let uu____9309 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9309 in
    let uu____9311 =
      let uu____9312 =
        let uu____9317 =
          let uu____9318 =
            let uu____9324 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[valid]], [aa], uu____9324) in
          FStar_SMTEncoding_Util.mkForall uu____9318 in
        (uu____9317, (Some "not interpretation"), (Some "l_not-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9312 in
    [uu____9311] in
  let mk_forall_interp env for_all tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x = FStar_SMTEncoding_Util.mkFreeV xx in
    let valid =
      let uu____9361 =
        let uu____9365 =
          let uu____9367 = FStar_SMTEncoding_Util.mkApp (for_all, [a; b]) in
          [uu____9367] in
        ("Valid", uu____9365) in
      FStar_SMTEncoding_Util.mkApp uu____9361 in
    let valid_b_x =
      let uu____9371 =
        let uu____9375 =
          let uu____9377 = FStar_SMTEncoding_Util.mk_ApplyTT b x in
          [uu____9377] in
        ("Valid", uu____9375) in
      FStar_SMTEncoding_Util.mkApp uu____9371 in
    let uu____9379 =
      let uu____9380 =
        let uu____9385 =
          let uu____9386 =
            let uu____9392 =
              let uu____9393 =
                let uu____9396 =
                  let uu____9397 =
                    let uu____9403 =
                      let uu____9406 =
                        let uu____9408 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x a in
                        [uu____9408] in
                      [uu____9406] in
                    let uu____9411 =
                      let uu____9412 =
                        let uu____9415 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x a in
                        (uu____9415, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9412 in
                    (uu____9403, [xx], uu____9411) in
                  FStar_SMTEncoding_Util.mkForall uu____9397 in
                (uu____9396, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9393 in
            ([[valid]], [aa; bb], uu____9392) in
          FStar_SMTEncoding_Util.mkForall uu____9386 in
        (uu____9385, (Some "forall interpretation"), (Some "forall-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9380 in
    [uu____9379] in
  let mk_exists_interp env for_some tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x = FStar_SMTEncoding_Util.mkFreeV xx in
    let valid =
      let uu____9463 =
        let uu____9467 =
          let uu____9469 = FStar_SMTEncoding_Util.mkApp (for_some, [a; b]) in
          [uu____9469] in
        ("Valid", uu____9467) in
      FStar_SMTEncoding_Util.mkApp uu____9463 in
    let valid_b_x =
      let uu____9473 =
        let uu____9477 =
          let uu____9479 = FStar_SMTEncoding_Util.mk_ApplyTT b x in
          [uu____9479] in
        ("Valid", uu____9477) in
      FStar_SMTEncoding_Util.mkApp uu____9473 in
    let uu____9481 =
      let uu____9482 =
        let uu____9487 =
          let uu____9488 =
            let uu____9494 =
              let uu____9495 =
                let uu____9498 =
                  let uu____9499 =
                    let uu____9505 =
                      let uu____9508 =
                        let uu____9510 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x a in
                        [uu____9510] in
                      [uu____9508] in
                    let uu____9513 =
                      let uu____9514 =
                        let uu____9517 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x a in
                        (uu____9517, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9514 in
                    (uu____9505, [xx], uu____9513) in
                  FStar_SMTEncoding_Util.mkExists uu____9499 in
                (uu____9498, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9495 in
            ([[valid]], [aa; bb], uu____9494) in
          FStar_SMTEncoding_Util.mkForall uu____9488 in
        (uu____9487, (Some "exists interpretation"), (Some "exists-interp")) in
      FStar_SMTEncoding_Term.Assume uu____9482 in
    [uu____9481] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9554 =
      let uu____9555 =
        let uu____9560 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9561 =
          let uu____9563 = varops.mk_unique "typing_range_const" in
          Some uu____9563 in
        (uu____9560, (Some "Range_const typing"), uu____9561) in
      FStar_SMTEncoding_Term.Assume uu____9555 in
    [uu____9554] in
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
          let uu____9826 =
            FStar_Util.find_opt
              (fun uu____9844  ->
                 match uu____9844 with
                 | (l,uu____9854) -> FStar_Ident.lid_equals l t) prims in
          match uu____9826 with
          | None  -> []
          | Some (uu____9876,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9913 = encode_function_type_as_formula None None t env in
        match uu____9913 with
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
            let uu____9946 =
              (let uu____9947 =
                 FStar_Syntax_Util.is_pure_or_ghost_function t_norm in
               FStar_All.pipe_left Prims.op_Negation uu____9947) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            match uu____9946 with
            | true  ->
                let uu____9951 = new_term_constant_and_tok_from_lid env lid in
                (match uu____9951 with
                 | (vname,vtok,env) ->
                     let arg_sorts =
                       let uu____9963 =
                         let uu____9964 = FStar_Syntax_Subst.compress t_norm in
                         uu____9964.FStar_Syntax_Syntax.n in
                       match uu____9963 with
                       | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9969) ->
                           FStar_All.pipe_right binders
                             (FStar_List.map
                                (fun uu____9986  ->
                                   FStar_SMTEncoding_Term.Term_sort))
                       | uu____9989 -> [] in
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
            | uu____9997 ->
                let uu____9998 = prims.is lid in
                (match uu____9998 with
                 | true  ->
                     let vname = varops.new_fvar lid in
                     let uu____10003 = prims.mk lid vname in
                     (match uu____10003 with
                      | (tok,definition) ->
                          let env = push_free_var env lid vname (Some tok) in
                          (definition, env))
                 | uu____10016 ->
                     let encode_non_total_function_typ =
                       lid.FStar_Ident.nsstr <> "Prims" in
                     let uu____10018 =
                       let uu____10024 = curried_arrow_formals_comp t_norm in
                       match uu____10024 with
                       | (args,comp) ->
                           (match encode_non_total_function_typ with
                            | true  ->
                                let uu____10039 =
                                  FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                    env.tcenv comp in
                                (args, uu____10039)
                            | uu____10046 ->
                                (args,
                                  (None,
                                    (FStar_Syntax_Util.comp_result comp)))) in
                     (match uu____10018 with
                      | (formals,(pre_opt,res_t)) ->
                          let uu____10066 =
                            new_term_constant_and_tok_from_lid env lid in
                          (match uu____10066 with
                           | (vname,vtok,env) ->
                               let vtok_tm =
                                 match formals with
                                 | [] ->
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (vname,
                                         FStar_SMTEncoding_Term.Term_sort)
                                 | uu____10079 ->
                                     FStar_SMTEncoding_Util.mkApp (vtok, []) in
                               let mk_disc_proj_axioms guard encoded_res_t
                                 vapp vars =
                                 FStar_All.pipe_right quals
                                   (FStar_List.collect
                                      (fun uu___123_10103  ->
                                         match uu___123_10103 with
                                         | FStar_Syntax_Syntax.Discriminator
                                             d ->
                                             let uu____10106 =
                                               FStar_Util.prefix vars in
                                             (match uu____10106 with
                                              | (uu____10117,(xxsym,uu____10119))
                                                  ->
                                                  let xx =
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                      (xxsym,
                                                        FStar_SMTEncoding_Term.Term_sort) in
                                                  let uu____10129 =
                                                    let uu____10130 =
                                                      let uu____10135 =
                                                        let uu____10136 =
                                                          let uu____10142 =
                                                            let uu____10143 =
                                                              let uu____10146
                                                                =
                                                                let uu____10147
                                                                  =
                                                                  FStar_SMTEncoding_Term.mk_tester
                                                                    (
                                                                    escape
                                                                    d.FStar_Ident.str)
                                                                    xx in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                  uu____10147 in
                                                              (vapp,
                                                                uu____10146) in
                                                            FStar_SMTEncoding_Util.mkEq
                                                              uu____10143 in
                                                          ([[vapp]], vars,
                                                            uu____10142) in
                                                        FStar_SMTEncoding_Util.mkForall
                                                          uu____10136 in
                                                      (uu____10135,
                                                        (Some
                                                           "Discriminator equation"),
                                                        (Some
                                                           (Prims.strcat
                                                              "disc_equation_"
                                                              (escape
                                                                 d.FStar_Ident.str)))) in
                                                    FStar_SMTEncoding_Term.Assume
                                                      uu____10130 in
                                                  [uu____10129])
                                         | FStar_Syntax_Syntax.Projector
                                             (d,f) ->
                                             let uu____10159 =
                                               FStar_Util.prefix vars in
                                             (match uu____10159 with
                                              | (uu____10170,(xxsym,uu____10172))
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
                                                  let uu____10186 =
                                                    let uu____10187 =
                                                      let uu____10192 =
                                                        let uu____10193 =
                                                          let uu____10199 =
                                                            FStar_SMTEncoding_Util.mkEq
                                                              (vapp,
                                                                prim_app) in
                                                          ([[vapp]], vars,
                                                            uu____10199) in
                                                        FStar_SMTEncoding_Util.mkForall
                                                          uu____10193 in
                                                      (uu____10192,
                                                        (Some
                                                           "Projector equation"),
                                                        (Some
                                                           (Prims.strcat
                                                              "proj_equation_"
                                                              tp_name))) in
                                                    FStar_SMTEncoding_Term.Assume
                                                      uu____10187 in
                                                  [uu____10186])
                                         | uu____10209 -> [])) in
                               let uu____10210 =
                                 encode_binders None formals env in
                               (match uu____10210 with
                                | (vars,guards,env',decls1,uu____10226) ->
                                    let uu____10233 =
                                      match pre_opt with
                                      | None  ->
                                          let uu____10238 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              guards in
                                          (uu____10238, decls1)
                                      | Some p ->
                                          let uu____10240 =
                                            encode_formula p env' in
                                          (match uu____10240 with
                                           | (g,ds) ->
                                               let uu____10247 =
                                                 FStar_SMTEncoding_Util.mk_and_l
                                                   (g :: guards) in
                                               (uu____10247,
                                                 (FStar_List.append decls1 ds))) in
                                    (match uu____10233 with
                                     | (guard,decls1) ->
                                         let vtok_app = mk_Apply vtok_tm vars in
                                         let vapp =
                                           let uu____10256 =
                                             let uu____10260 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 vars in
                                             (vname, uu____10260) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____10256 in
                                         let uu____10265 =
                                           let vname_decl =
                                             let uu____10270 =
                                               let uu____10276 =
                                                 FStar_All.pipe_right formals
                                                   (FStar_List.map
                                                      (fun uu____10281  ->
                                                         FStar_SMTEncoding_Term.Term_sort)) in
                                               (vname, uu____10276,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 None) in
                                             FStar_SMTEncoding_Term.DeclFun
                                               uu____10270 in
                                           let uu____10286 =
                                             let env =
                                               let uu___151_10290 = env in
                                               {
                                                 bindings =
                                                   (uu___151_10290.bindings);
                                                 depth =
                                                   (uu___151_10290.depth);
                                                 tcenv =
                                                   (uu___151_10290.tcenv);
                                                 warn = (uu___151_10290.warn);
                                                 cache =
                                                   (uu___151_10290.cache);
                                                 nolabels =
                                                   (uu___151_10290.nolabels);
                                                 use_zfuel_name =
                                                   (uu___151_10290.use_zfuel_name);
                                                 encode_non_total_function_typ
                                               } in
                                             let uu____10291 =
                                               let uu____10292 =
                                                 head_normal env tt in
                                               Prims.op_Negation uu____10292 in
                                             match uu____10291 with
                                             | true  ->
                                                 encode_term_pred None tt env
                                                   vtok_tm
                                             | uu____10295 ->
                                                 encode_term_pred None t_norm
                                                   env vtok_tm in
                                           match uu____10286 with
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
                                               let uu____10304 =
                                                 match formals with
                                                 | [] ->
                                                     let uu____10313 =
                                                       let uu____10314 =
                                                         let uu____10316 =
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                             (vname,
                                                               FStar_SMTEncoding_Term.Term_sort) in
                                                         FStar_All.pipe_left
                                                           (fun _0_34  ->
                                                              Some _0_34)
                                                           uu____10316 in
                                                       push_free_var env lid
                                                         vname uu____10314 in
                                                     ((FStar_List.append
                                                         decls2 [tok_typing]),
                                                       uu____10313)
                                                 | uu____10319 ->
                                                     let vtok_decl =
                                                       FStar_SMTEncoding_Term.DeclFun
                                                         (vtok, [],
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           None) in
                                                     let vtok_fresh =
                                                       let uu____10324 =
                                                         varops.next_id () in
                                                       FStar_SMTEncoding_Term.fresh_token
                                                         (vtok,
                                                           FStar_SMTEncoding_Term.Term_sort)
                                                         uu____10324 in
                                                     let name_tok_corr =
                                                       let uu____10326 =
                                                         let uu____10331 =
                                                           let uu____10332 =
                                                             let uu____10338
                                                               =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (vtok_app,
                                                                   vapp) in
                                                             ([[vtok_app];
                                                              [vapp]], vars,
                                                               uu____10338) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____10332 in
                                                         (uu____10331,
                                                           (Some
                                                              "Name-token correspondence"),
                                                           (Some
                                                              (Prims.strcat
                                                                 "token_correspondence_"
                                                                 vname))) in
                                                       FStar_SMTEncoding_Term.Assume
                                                         uu____10326 in
                                                     ((FStar_List.append
                                                         decls2
                                                         [vtok_decl;
                                                         vtok_fresh;
                                                         name_tok_corr;
                                                         tok_typing]), env) in
                                               (match uu____10304 with
                                                | (tok_decl,env) ->
                                                    ((vname_decl ::
                                                      tok_decl), env)) in
                                         (match uu____10265 with
                                          | (decls2,env) ->
                                              let uu____10363 =
                                                let res_t =
                                                  FStar_Syntax_Subst.compress
                                                    res_t in
                                                let uu____10368 =
                                                  encode_term res_t env' in
                                                match uu____10368 with
                                                | (encoded_res_t,decls) ->
                                                    let uu____10376 =
                                                      FStar_SMTEncoding_Term.mk_HasType
                                                        vapp encoded_res_t in
                                                    (encoded_res_t,
                                                      uu____10376, decls) in
                                              (match uu____10363 with
                                               | (encoded_res_t,ty_pred,decls3)
                                                   ->
                                                   let typingAx =
                                                     let uu____10384 =
                                                       let uu____10389 =
                                                         let uu____10390 =
                                                           let uu____10396 =
                                                             FStar_SMTEncoding_Util.mkImp
                                                               (guard,
                                                                 ty_pred) in
                                                           ([[vapp]], vars,
                                                             uu____10396) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____10390 in
                                                       (uu____10389,
                                                         (Some
                                                            "free var typing"),
                                                         (Some
                                                            (Prims.strcat
                                                               "typing_"
                                                               vname))) in
                                                     FStar_SMTEncoding_Term.Assume
                                                       uu____10384 in
                                                   let freshness =
                                                     let uu____10406 =
                                                       FStar_All.pipe_right
                                                         quals
                                                         (FStar_List.contains
                                                            FStar_Syntax_Syntax.New) in
                                                     match uu____10406 with
                                                     | true  ->
                                                         let uu____10409 =
                                                           let uu____10410 =
                                                             let uu____10416
                                                               =
                                                               FStar_All.pipe_right
                                                                 vars
                                                                 (FStar_List.map
                                                                    Prims.snd) in
                                                             let uu____10422
                                                               =
                                                               varops.next_id
                                                                 () in
                                                             (vname,
                                                               uu____10416,
                                                               FStar_SMTEncoding_Term.Term_sort,
                                                               uu____10422) in
                                                           FStar_SMTEncoding_Term.fresh_constructor
                                                             uu____10410 in
                                                         let uu____10424 =
                                                           let uu____10426 =
                                                             pretype_axiom
                                                               vapp vars in
                                                           [uu____10426] in
                                                         uu____10409 ::
                                                           uu____10424
                                                     | uu____10427 -> [] in
                                                   let g =
                                                     let uu____10430 =
                                                       let uu____10432 =
                                                         let uu____10434 =
                                                           let uu____10436 =
                                                             let uu____10438
                                                               =
                                                               mk_disc_proj_axioms
                                                                 guard
                                                                 encoded_res_t
                                                                 vapp vars in
                                                             typingAx ::
                                                               uu____10438 in
                                                           FStar_List.append
                                                             freshness
                                                             uu____10436 in
                                                         FStar_List.append
                                                           decls3 uu____10434 in
                                                       FStar_List.append
                                                         decls2 uu____10432 in
                                                     FStar_List.append decls1
                                                       uu____10430 in
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
          let uu____10460 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10460 with
          | None  ->
              let uu____10483 = encode_free_var env x t t_norm [] in
              (match uu____10483 with
               | (decls,env) ->
                   let uu____10498 =
                     lookup_lid env
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10498 with
                    | (n,x',uu____10517) -> ((n, x'), decls, env)))
          | Some (n,x,uu____10529) -> ((n, x), [], env)
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
          let uu____10562 = encode_free_var env lid t tt quals in
          match uu____10562 with
          | (decls,env) ->
              let uu____10573 = FStar_Syntax_Util.is_smt_lemma t in
              (match uu____10573 with
               | true  ->
                   let uu____10577 =
                     let uu____10579 = encode_smt_lemma env lid tt in
                     FStar_List.append decls uu____10579 in
                   (uu____10577, env)
               | uu____10582 -> (decls, env))
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
             (fun uu____10607  ->
                fun lb  ->
                  match uu____10607 with
                  | (decls,env) ->
                      let uu____10619 =
                        let uu____10623 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env uu____10623
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10619 with
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
    fun uu____10647  ->
      fun quals  ->
        match uu____10647 with
        | (is_rec,bindings) ->
            let eta_expand binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10696 = FStar_Util.first_N nbinders formals in
              match uu____10696 with
              | (formals,extra_formals) ->
                  let subst =
                    FStar_List.map2
                      (fun uu____10736  ->
                         fun uu____10737  ->
                           match (uu____10736, uu____10737) with
                           | ((formal,uu____10747),(binder,uu____10749)) ->
                               let uu____10754 =
                                 let uu____10759 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10759) in
                               FStar_Syntax_Syntax.NT uu____10754) formals
                      binders in
                  let extra_formals =
                    let uu____10764 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10778  ->
                              match uu____10778 with
                              | (x,i) ->
                                  let uu____10785 =
                                    let uu___152_10786 = x in
                                    let uu____10787 =
                                      FStar_Syntax_Subst.subst subst
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___152_10786.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___152_10786.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10787
                                    } in
                                  (uu____10785, i))) in
                    FStar_All.pipe_right uu____10764
                      FStar_Syntax_Util.name_binders in
                  let body =
                    let uu____10799 =
                      let uu____10801 =
                        let uu____10802 = FStar_Syntax_Subst.subst subst t in
                        uu____10802.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10801 in
                    let uu____10806 =
                      let uu____10807 = FStar_Syntax_Subst.compress body in
                      let uu____10808 =
                        let uu____10809 =
                          FStar_Syntax_Util.args_of_binders extra_formals in
                        FStar_All.pipe_left Prims.snd uu____10809 in
                      FStar_Syntax_Syntax.extend_app_n uu____10807
                        uu____10808 in
                    uu____10806 uu____10799 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals), body) in
            let destruct_bound_function flid t_norm e =
              let rec aux norm t_norm =
                let uu____10868 = FStar_Syntax_Util.abs_formals e in
                match uu____10868 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____10921::uu____10922 ->
                         let uu____10930 =
                           let uu____10931 =
                             FStar_Syntax_Subst.compress t_norm in
                           uu____10931.FStar_Syntax_Syntax.n in
                         (match uu____10930 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____10960 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____10960 with
                               | (formals,c) ->
                                   let nformals = FStar_List.length formals in
                                   let nbinders = FStar_List.length binders in
                                   let tres = FStar_Syntax_Util.comp_result c in
                                   let uu____10990 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c) in
                                   (match uu____10990 with
                                    | true  ->
                                        let uu____11010 =
                                          FStar_Util.first_N nformals binders in
                                        (match uu____11010 with
                                         | (bs0,rest) ->
                                             let c =
                                               let subst =
                                                 FStar_List.map2
                                                   (fun uu____11058  ->
                                                      fun uu____11059  ->
                                                        match (uu____11058,
                                                                uu____11059)
                                                        with
                                                        | ((x,uu____11069),
                                                           (b,uu____11071))
                                                            ->
                                                            let uu____11076 =
                                                              let uu____11081
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  b in
                                                              (x,
                                                                uu____11081) in
                                                            FStar_Syntax_Syntax.NT
                                                              uu____11076)
                                                   formals bs0 in
                                               FStar_Syntax_Subst.subst_comp
                                                 subst c in
                                             let body =
                                               FStar_Syntax_Util.abs rest
                                                 body lopt in
                                             ((bs0, body, bs0,
                                                (FStar_Syntax_Util.comp_result
                                                   c)), false))
                                    | uu____11103 ->
                                        (match nformals > nbinders with
                                         | true  ->
                                             let uu____11123 =
                                               eta_expand binders formals
                                                 body tres in
                                             (match uu____11123 with
                                              | (binders,body) ->
                                                  ((binders, body, formals,
                                                     tres), false))
                                         | uu____11175 ->
                                             ((binders, body, formals, tres),
                                               false))))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11185) ->
                              let uu____11190 =
                                let uu____11203 =
                                  aux norm x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11203 in
                              (uu____11190, true)
                          | uu____11242 when Prims.op_Negation norm ->
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
                          | uu____11244 ->
                              let uu____11245 =
                                let uu____11246 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11247 =
                                  FStar_Syntax_Print.term_to_string t_norm in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11246
                                  uu____11247 in
                              failwith uu____11245)
                     | uu____11262 ->
                         let uu____11263 =
                           let uu____11264 =
                             FStar_Syntax_Subst.compress t_norm in
                           uu____11264.FStar_Syntax_Syntax.n in
                         (match uu____11263 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11293 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11293 with
                               | (formals,c) ->
                                   let tres = FStar_Syntax_Util.comp_result c in
                                   let uu____11315 =
                                     eta_expand [] formals e tres in
                                   (match uu____11315 with
                                    | (binders,body) ->
                                        ((binders, body, formals, tres),
                                          false)))
                          | uu____11369 -> (([], e, [], t_norm), false))) in
              aux false t_norm in
            (try
               let uu____11397 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         FStar_Syntax_Util.is_lemma
                           lb.FStar_Syntax_Syntax.lbtyp)) in
               match uu____11397 with
               | true  -> encode_top_level_vals env bindings quals
               | uu____11403 ->
                   let uu____11404 =
                     FStar_All.pipe_right bindings
                       (FStar_List.fold_left
                          (fun uu____11445  ->
                             fun lb  ->
                               match uu____11445 with
                               | (toks,typs,decls,env) ->
                                   ((let uu____11496 =
                                       FStar_Syntax_Util.is_lemma
                                         lb.FStar_Syntax_Syntax.lbtyp in
                                     match uu____11496 with
                                     | true  ->
                                         Prims.raise Let_rec_unencodeable
                                     | uu____11497 -> ());
                                    (let t_norm =
                                       whnf env lb.FStar_Syntax_Syntax.lbtyp in
                                     let uu____11499 =
                                       let uu____11507 =
                                         FStar_Util.right
                                           lb.FStar_Syntax_Syntax.lbname in
                                       declare_top_level_let env uu____11507
                                         lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                     match uu____11499 with
                                     | (tok,decl,env) ->
                                         let uu____11532 =
                                           let uu____11539 =
                                             let uu____11545 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             (uu____11545, tok) in
                                           uu____11539 :: toks in
                                         (uu____11532, (t_norm :: typs),
                                           (decl :: decls), env))))
                          ([], [], [], env)) in
                   (match uu____11404 with
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
                          | uu____11647 ->
                              (match curry with
                               | true  ->
                                   (match ftok with
                                    | Some ftok -> mk_Apply ftok vars
                                    | None  ->
                                        let uu____11652 =
                                          FStar_SMTEncoding_Util.mkFreeV
                                            (f,
                                              FStar_SMTEncoding_Term.Term_sort) in
                                        mk_Apply uu____11652 vars)
                               | uu____11653 ->
                                   let uu____11654 =
                                     let uu____11658 =
                                       FStar_List.map
                                         FStar_SMTEncoding_Util.mkFreeV vars in
                                     (f, uu____11658) in
                                   FStar_SMTEncoding_Util.mkApp uu____11654) in
                        let uu____11663 =
                          (FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___124_11665  ->
                                   match uu___124_11665 with
                                   | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                       true
                                   | uu____11666 -> false)))
                            ||
                            (FStar_All.pipe_right typs
                               (FStar_Util.for_some
                                  (fun t  ->
                                     let uu____11669 =
                                       FStar_Syntax_Util.is_pure_or_ghost_function
                                         t in
                                     FStar_All.pipe_left Prims.op_Negation
                                       uu____11669))) in
                        (match uu____11663 with
                         | true  -> (decls, env)
                         | uu____11674 ->
                             (match Prims.op_Negation is_rec with
                              | true  ->
                                  (match (bindings, typs, toks) with
                                   | ({
                                        FStar_Syntax_Syntax.lbname =
                                          uu____11689;
                                        FStar_Syntax_Syntax.lbunivs =
                                          uu____11690;
                                        FStar_Syntax_Syntax.lbtyp =
                                          uu____11691;
                                        FStar_Syntax_Syntax.lbeff =
                                          uu____11692;
                                        FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                                      (flid_fv,(f,ftok))::[]) ->
                                       let e = FStar_Syntax_Subst.compress e in
                                       let flid =
                                         (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                       let uu____11734 =
                                         destruct_bound_function flid t_norm
                                           e in
                                       (match uu____11734 with
                                        | ((binders,body,uu____11746,uu____11747),curry)
                                            ->
                                            ((let uu____11754 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env.tcenv)
                                                  (FStar_Options.Other
                                                     "SMTEncoding") in
                                              match uu____11754 with
                                              | true  ->
                                                  let uu____11755 =
                                                    FStar_Syntax_Print.binders_to_string
                                                      ", " binders in
                                                  let uu____11756 =
                                                    FStar_Syntax_Print.term_to_string
                                                      body in
                                                  FStar_Util.print2
                                                    "Encoding let : binders=[%s], body=%s\n"
                                                    uu____11755 uu____11756
                                              | uu____11757 -> ());
                                             (let uu____11758 =
                                                encode_binders None binders
                                                  env in
                                              match uu____11758 with
                                              | (vars,guards,env',binder_decls,uu____11774)
                                                  ->
                                                  let app =
                                                    mk_app curry f ftok vars in
                                                  let uu____11782 =
                                                    let uu____11787 =
                                                      FStar_All.pipe_right
                                                        quals
                                                        (FStar_List.contains
                                                           FStar_Syntax_Syntax.Logic) in
                                                    match uu____11787 with
                                                    | true  ->
                                                        let uu____11793 =
                                                          FStar_SMTEncoding_Term.mk_Valid
                                                            app in
                                                        let uu____11794 =
                                                          encode_formula body
                                                            env' in
                                                        (uu____11793,
                                                          uu____11794)
                                                    | uu____11799 ->
                                                        let uu____11800 =
                                                          encode_term body
                                                            env' in
                                                        (app, uu____11800) in
                                                  (match uu____11782 with
                                                   | (app,(body,decls2)) ->
                                                       let eqn =
                                                         let uu____11814 =
                                                           let uu____11819 =
                                                             let uu____11820
                                                               =
                                                               let uu____11826
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkEq
                                                                   (app,
                                                                    body) in
                                                               ([[app]],
                                                                 vars,
                                                                 uu____11826) in
                                                             FStar_SMTEncoding_Util.mkForall
                                                               uu____11820 in
                                                           let uu____11832 =
                                                             let uu____11834
                                                               =
                                                               FStar_Util.format1
                                                                 "Equation for %s"
                                                                 flid.FStar_Ident.str in
                                                             Some uu____11834 in
                                                           (uu____11819,
                                                             uu____11832,
                                                             (Some
                                                                (Prims.strcat
                                                                   "equation_"
                                                                   f))) in
                                                         FStar_SMTEncoding_Term.Assume
                                                           uu____11814 in
                                                       let uu____11837 =
                                                         let uu____11839 =
                                                           let uu____11841 =
                                                             let uu____11843
                                                               =
                                                               let uu____11845
                                                                 =
                                                                 primitive_type_axioms
                                                                   env.tcenv
                                                                   flid f app in
                                                               FStar_List.append
                                                                 [eqn]
                                                                 uu____11845 in
                                                             FStar_List.append
                                                               decls2
                                                               uu____11843 in
                                                           FStar_List.append
                                                             binder_decls
                                                             uu____11841 in
                                                         FStar_List.append
                                                           decls uu____11839 in
                                                       (uu____11837, env)))))
                                   | uu____11848 -> failwith "Impossible")
                              | uu____11863 ->
                                  let fuel =
                                    let uu____11867 = varops.fresh "fuel" in
                                    (uu____11867,
                                      FStar_SMTEncoding_Term.Fuel_sort) in
                                  let fuel_tm =
                                    FStar_SMTEncoding_Util.mkFreeV fuel in
                                  let env0 = env in
                                  let uu____11870 =
                                    FStar_All.pipe_right toks
                                      (FStar_List.fold_left
                                         (fun uu____11909  ->
                                            fun uu____11910  ->
                                              match (uu____11909,
                                                      uu____11910)
                                              with
                                              | ((gtoks,env),(flid_fv,
                                                              (f,ftok)))
                                                  ->
                                                  let flid =
                                                    (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                                  let g =
                                                    let uu____11992 =
                                                      FStar_Ident.lid_add_suffix
                                                        flid
                                                        "fuel_instrumented" in
                                                    varops.new_fvar
                                                      uu____11992 in
                                                  let gtok =
                                                    let uu____11994 =
                                                      FStar_Ident.lid_add_suffix
                                                        flid
                                                        "fuel_instrumented_token" in
                                                    varops.new_fvar
                                                      uu____11994 in
                                                  let env =
                                                    let uu____11996 =
                                                      let uu____11998 =
                                                        FStar_SMTEncoding_Util.mkApp
                                                          (g, [fuel_tm]) in
                                                      FStar_All.pipe_left
                                                        (fun _0_36  ->
                                                           Some _0_36)
                                                        uu____11998 in
                                                    push_free_var env flid
                                                      gtok uu____11996 in
                                                  (((flid, f, ftok, g, gtok)
                                                    :: gtoks), env))
                                         ([], env)) in
                                  (match uu____11870 with
                                   | (gtoks,env) ->
                                       let gtoks = FStar_List.rev gtoks in
                                       let encode_one_binding env0
                                         uu____12082 t_norm uu____12084 =
                                         match (uu____12082, uu____12084)
                                         with
                                         | ((flid,f,ftok,g,gtok),{
                                                                   FStar_Syntax_Syntax.lbname
                                                                    = lbn;
                                                                   FStar_Syntax_Syntax.lbunivs
                                                                    =
                                                                    uu____12108;
                                                                   FStar_Syntax_Syntax.lbtyp
                                                                    =
                                                                    uu____12109;
                                                                   FStar_Syntax_Syntax.lbeff
                                                                    =
                                                                    uu____12110;
                                                                   FStar_Syntax_Syntax.lbdef
                                                                    = e;_})
                                             ->
                                             ((let uu____12128 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env0.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               match uu____12128 with
                                               | true  ->
                                                   let uu____12129 =
                                                     FStar_Syntax_Print.lbname_to_string
                                                       lbn in
                                                   let uu____12130 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t_norm in
                                                   let uu____12131 =
                                                     FStar_Syntax_Print.term_to_string
                                                       e in
                                                   FStar_Util.print3
                                                     "Encoding let rec %s : %s = %s\n"
                                                     uu____12129 uu____12130
                                                     uu____12131
                                               | uu____12132 -> ());
                                              (let uu____12133 =
                                                 destruct_bound_function flid
                                                   t_norm e in
                                               match uu____12133 with
                                               | ((binders,body,formals,tres),curry)
                                                   ->
                                                   ((let uu____12155 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env0.tcenv)
                                                         (FStar_Options.Other
                                                            "SMTEncoding") in
                                                     match uu____12155 with
                                                     | true  ->
                                                         let uu____12156 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", " binders in
                                                         let uu____12157 =
                                                           FStar_Syntax_Print.term_to_string
                                                             body in
                                                         let uu____12158 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", " formals in
                                                         let uu____12159 =
                                                           FStar_Syntax_Print.term_to_string
                                                             tres in
                                                         FStar_Util.print4
                                                           "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                           uu____12156
                                                           uu____12157
                                                           uu____12158
                                                           uu____12159
                                                     | uu____12160 -> ());
                                                    (match curry with
                                                     | true  ->
                                                         failwith
                                                           "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                     | uu____12162 -> ());
                                                    (let uu____12163 =
                                                       encode_binders None
                                                         binders env in
                                                     match uu____12163 with
                                                     | (vars,guards,env',binder_decls,uu____12181)
                                                         ->
                                                         let decl_g =
                                                           let uu____12189 =
                                                             let uu____12195
                                                               =
                                                               let uu____12197
                                                                 =
                                                                 FStar_List.map
                                                                   Prims.snd
                                                                   vars in
                                                               FStar_SMTEncoding_Term.Fuel_sort
                                                                 ::
                                                                 uu____12197 in
                                                             (g, uu____12195,
                                                               FStar_SMTEncoding_Term.Term_sort,
                                                               (Some
                                                                  "Fuel-instrumented function name")) in
                                                           FStar_SMTEncoding_Term.DeclFun
                                                             uu____12189 in
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
                                                           let uu____12212 =
                                                             let uu____12216
                                                               =
                                                               FStar_List.map
                                                                 FStar_SMTEncoding_Util.mkFreeV
                                                                 vars in
                                                             (f, uu____12216) in
                                                           FStar_SMTEncoding_Util.mkApp
                                                             uu____12212 in
                                                         let gsapp =
                                                           let uu____12222 =
                                                             let uu____12226
                                                               =
                                                               let uu____12228
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkApp
                                                                   ("SFuel",
                                                                    [fuel_tm]) in
                                                               uu____12228 ::
                                                                 vars_tm in
                                                             (g, uu____12226) in
                                                           FStar_SMTEncoding_Util.mkApp
                                                             uu____12222 in
                                                         let gmax =
                                                           let uu____12232 =
                                                             let uu____12236
                                                               =
                                                               let uu____12238
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkApp
                                                                   ("MaxFuel",
                                                                    []) in
                                                               uu____12238 ::
                                                                 vars_tm in
                                                             (g, uu____12236) in
                                                           FStar_SMTEncoding_Util.mkApp
                                                             uu____12232 in
                                                         let uu____12241 =
                                                           encode_term body
                                                             env' in
                                                         (match uu____12241
                                                          with
                                                          | (body_tm,decls2)
                                                              ->
                                                              let eqn_g =
                                                                let uu____12252
                                                                  =
                                                                  let uu____12257
                                                                    =
                                                                    let uu____12258
                                                                    =
                                                                    let uu____12266
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
                                                                    uu____12266) in
                                                                    FStar_SMTEncoding_Util.mkForall'
                                                                    uu____12258 in
                                                                  let uu____12277
                                                                    =
                                                                    let uu____12279
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                    Some
                                                                    uu____12279 in
                                                                  (uu____12257,
                                                                    uu____12277,
                                                                    (
                                                                    Some
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))) in
                                                                FStar_SMTEncoding_Term.Assume
                                                                  uu____12252 in
                                                              let eqn_f =
                                                                let uu____12283
                                                                  =
                                                                  let uu____12288
                                                                    =
                                                                    let uu____12289
                                                                    =
                                                                    let uu____12295
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____12295) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12289 in
                                                                  (uu____12288,
                                                                    (
                                                                    Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (
                                                                    Some
                                                                    (Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g))) in
                                                                FStar_SMTEncoding_Term.Assume
                                                                  uu____12283 in
                                                              let eqn_g' =
                                                                let uu____12304
                                                                  =
                                                                  let uu____12309
                                                                    =
                                                                    let uu____12310
                                                                    =
                                                                    let uu____12316
                                                                    =
                                                                    let uu____12317
                                                                    =
                                                                    let uu____12320
                                                                    =
                                                                    let uu____12321
                                                                    =
                                                                    let uu____12325
                                                                    =
                                                                    let uu____12327
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12327
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12325) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12321 in
                                                                    (gsapp,
                                                                    uu____12320) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12317 in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12316) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12310 in
                                                                  (uu____12309,
                                                                    (
                                                                    Some
                                                                    "Fuel irrelevance"),
                                                                    (
                                                                    Some
                                                                    (Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g))) in
                                                                FStar_SMTEncoding_Term.Assume
                                                                  uu____12304 in
                                                              let uu____12340
                                                                =
                                                                let uu____12345
                                                                  =
                                                                  encode_binders
                                                                    None
                                                                    formals
                                                                    env0 in
                                                                match uu____12345
                                                                with
                                                                | (vars,v_guards,env,binder_decls,uu____12362)
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
                                                                    let uu____12377
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12377
                                                                    (fuel ::
                                                                    vars) in
                                                                    let uu____12380
                                                                    =
                                                                    let uu____12385
                                                                    =
                                                                    let uu____12386
                                                                    =
                                                                    let uu____12392
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12392) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12386 in
                                                                    (uu____12385,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12380 in
                                                                    let uu____12404
                                                                    =
                                                                    let uu____12408
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env gapp in
                                                                    match uu____12408
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____12416
                                                                    =
                                                                    let uu____12418
                                                                    =
                                                                    let uu____12419
                                                                    =
                                                                    let uu____12424
                                                                    =
                                                                    let uu____12425
                                                                    =
                                                                    let uu____12431
                                                                    =
                                                                    let uu____12432
                                                                    =
                                                                    let uu____12435
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12435,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12432 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12431) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12425 in
                                                                    (uu____12424,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12419 in
                                                                    [uu____12418] in
                                                                    (d3,
                                                                    uu____12416) in
                                                                    (match uu____12404
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
                                                              (match uu____12340
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
                                       let uu____12471 =
                                         let uu____12478 =
                                           FStar_List.zip3 gtoks typs
                                             bindings in
                                         FStar_List.fold_left
                                           (fun uu____12510  ->
                                              fun uu____12511  ->
                                                match (uu____12510,
                                                        uu____12511)
                                                with
                                                | ((decls,eqns,env0),
                                                   (gtok,ty,lb)) ->
                                                    let uu____12587 =
                                                      encode_one_binding env0
                                                        gtok ty lb in
                                                    (match uu____12587 with
                                                     | (decls',eqns',env0) ->
                                                         ((decls' :: decls),
                                                           (FStar_List.append
                                                              eqns' eqns),
                                                           env0)))
                                           ([decls], [], env0) uu____12478 in
                                       (match uu____12471 with
                                        | (decls,eqns,env0) ->
                                            let uu____12627 =
                                              let uu____12632 =
                                                FStar_All.pipe_right decls
                                                  FStar_List.flatten in
                                              FStar_All.pipe_right
                                                uu____12632
                                                (FStar_List.partition
                                                   (fun uu___125_12642  ->
                                                      match uu___125_12642
                                                      with
                                                      | FStar_SMTEncoding_Term.DeclFun
                                                          uu____12643 -> true
                                                      | uu____12649 -> false)) in
                                            (match uu____12627 with
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
                   let uu____12667 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12667
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
      (let uu____12700 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       match uu____12700 with
       | true  ->
           let uu____12701 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
             uu____12701
       | uu____12702 -> ());
      (let nm =
         let uu____12704 = FStar_Syntax_Util.lid_of_sigelt se in
         match uu____12704 with | None  -> "" | Some l -> l.FStar_Ident.str in
       let uu____12707 = encode_sigelt' env se in
       match uu____12707 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12716 =
                  let uu____12718 =
                    let uu____12719 = FStar_Util.format1 "<Skipped %s/>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12719 in
                  [uu____12718] in
                (uu____12716, e)
            | uu____12721 ->
                let uu____12722 =
                  let uu____12724 =
                    let uu____12726 =
                      let uu____12727 =
                        FStar_Util.format1 "<Start encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12727 in
                    uu____12726 :: g in
                  let uu____12728 =
                    let uu____12730 =
                      let uu____12731 =
                        FStar_Util.format1 "</end encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12731 in
                    [uu____12730] in
                  FStar_List.append uu____12724 uu____12728 in
                (uu____12722, e)))
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12739 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect (ed,uu____12750) ->
          let uu____12751 =
            let uu____12752 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12752 Prims.op_Negation in
          (match uu____12751 with
           | true  -> ([], env)
           | uu____12757 ->
               let close_effect_params tm =
                 match ed.FStar_Syntax_Syntax.binders with
                 | [] -> tm
                 | uu____12772 ->
                     let uu____12773 =
                       let uu____12776 =
                         let uu____12777 =
                           let uu____12792 =
                             FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                               (FStar_Util.Inr
                                  (FStar_Syntax_Const.effect_Tot_lid,
                                    [FStar_Syntax_Syntax.TOTAL])) in
                           ((ed.FStar_Syntax_Syntax.binders), tm,
                             uu____12792) in
                         FStar_Syntax_Syntax.Tm_abs uu____12777 in
                       FStar_Syntax_Syntax.mk uu____12776 in
                     uu____12773 None tm.FStar_Syntax_Syntax.pos in
               let encode_action env a =
                 let uu____12845 =
                   new_term_constant_and_tok_from_lid env
                     a.FStar_Syntax_Syntax.action_name in
                 match uu____12845 with
                 | (aname,atok,env) ->
                     let uu____12855 =
                       FStar_Syntax_Util.arrow_formals_comp
                         a.FStar_Syntax_Syntax.action_typ in
                     (match uu____12855 with
                      | (formals,uu____12865) ->
                          let uu____12872 =
                            let uu____12875 =
                              close_effect_params
                                a.FStar_Syntax_Syntax.action_defn in
                            encode_term uu____12875 env in
                          (match uu____12872 with
                           | (tm,decls) ->
                               let a_decls =
                                 let uu____12883 =
                                   let uu____12884 =
                                     let uu____12890 =
                                       FStar_All.pipe_right formals
                                         (FStar_List.map
                                            (fun uu____12898  ->
                                               FStar_SMTEncoding_Term.Term_sort)) in
                                     (aname, uu____12890,
                                       FStar_SMTEncoding_Term.Term_sort,
                                       (Some "Action")) in
                                   FStar_SMTEncoding_Term.DeclFun uu____12884 in
                                 [uu____12883;
                                 FStar_SMTEncoding_Term.DeclFun
                                   (atok, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action token"))] in
                               let uu____12905 =
                                 let aux uu____12934 uu____12935 =
                                   match (uu____12934, uu____12935) with
                                   | ((bv,uu____12962),(env,acc_sorts,acc))
                                       ->
                                       let uu____12983 = gen_term_var env bv in
                                       (match uu____12983 with
                                        | (xxsym,xx,env) ->
                                            (env,
                                              ((xxsym,
                                                 FStar_SMTEncoding_Term.Term_sort)
                                              :: acc_sorts), (xx :: acc))) in
                                 FStar_List.fold_right aux formals
                                   (env, [], []) in
                               (match uu____12905 with
                                | (uu____13021,xs_sorts,xs) ->
                                    let app =
                                      FStar_SMTEncoding_Util.mkApp
                                        (aname, xs) in
                                    let a_eq =
                                      let uu____13035 =
                                        let uu____13040 =
                                          let uu____13041 =
                                            let uu____13047 =
                                              let uu____13048 =
                                                let uu____13051 =
                                                  mk_Apply tm xs_sorts in
                                                (app, uu____13051) in
                                              FStar_SMTEncoding_Util.mkEq
                                                uu____13048 in
                                            ([[app]], xs_sorts, uu____13047) in
                                          FStar_SMTEncoding_Util.mkForall
                                            uu____13041 in
                                        (uu____13040,
                                          (Some "Action equality"),
                                          (Some
                                             (Prims.strcat aname "_equality"))) in
                                      FStar_SMTEncoding_Term.Assume
                                        uu____13035 in
                                    let tok_correspondence =
                                      let tok_term =
                                        FStar_SMTEncoding_Util.mkFreeV
                                          (atok,
                                            FStar_SMTEncoding_Term.Term_sort) in
                                      let tok_app =
                                        mk_Apply tok_term xs_sorts in
                                      let uu____13064 =
                                        let uu____13069 =
                                          let uu____13070 =
                                            let uu____13076 =
                                              FStar_SMTEncoding_Util.mkEq
                                                (tok_app, app) in
                                            ([[tok_app]], xs_sorts,
                                              uu____13076) in
                                          FStar_SMTEncoding_Util.mkForall
                                            uu____13070 in
                                        (uu____13069,
                                          (Some "Action token correspondence"),
                                          (Some
                                             (Prims.strcat aname
                                                "_token_correspondence"))) in
                                      FStar_SMTEncoding_Term.Assume
                                        uu____13064 in
                                    (env,
                                      (FStar_List.append decls
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])))))) in
               let uu____13087 =
                 FStar_Util.fold_map encode_action env
                   ed.FStar_Syntax_Syntax.actions in
               (match uu____13087 with
                | (env,decls2) -> ((FStar_List.flatten decls2), env)))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____13103,uu____13104,uu____13105,uu____13106) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13109 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13109 with | (tname,ttok,env) -> ([], env))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____13120,t,quals,uu____13123) ->
          let will_encode_definition =
            let uu____13127 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___126_13129  ->
                      match uu___126_13129 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13132 -> false)) in
            Prims.op_Negation uu____13127 in
          (match will_encode_definition with
           | true  -> ([], env)
           | uu____13136 ->
               let fv =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_constant None in
               let uu____13138 = encode_top_level_val env fv t quals in
               (match uu____13138 with
                | (decls,env) ->
                    let tname = lid.FStar_Ident.str in
                    let tsym =
                      FStar_SMTEncoding_Util.mkFreeV
                        (tname, FStar_SMTEncoding_Term.Term_sort) in
                    let uu____13150 =
                      let uu____13152 =
                        primitive_type_axioms env.tcenv lid tname tsym in
                      FStar_List.append decls uu____13152 in
                    (uu____13150, env)))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____13157,uu____13158) ->
          let uu____13161 = encode_formula f env in
          (match uu____13161 with
           | (f,decls) ->
               let g =
                 let uu____13170 =
                   let uu____13171 =
                     let uu____13176 =
                       let uu____13178 =
                         let uu____13179 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13179 in
                       Some uu____13178 in
                     let uu____13180 =
                       let uu____13182 =
                         varops.mk_unique
                           (Prims.strcat "assumption_" l.FStar_Ident.str) in
                       Some uu____13182 in
                     (f, uu____13176, uu____13180) in
                   FStar_SMTEncoding_Term.Assume uu____13171 in
                 [uu____13170] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,r,uu____13188,quals,uu____13190)
          when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13198 =
            FStar_Util.fold_map
              (fun env  ->
                 fun lb  ->
                   let lid =
                     let uu____13205 =
                       let uu____13210 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13210.FStar_Syntax_Syntax.fv_name in
                     uu____13205.FStar_Syntax_Syntax.v in
                   let uu____13214 =
                     let uu____13215 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13215 in
                   match uu____13214 with
                   | true  ->
                       let val_decl =
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp), quals, r) in
                       let uu____13234 = encode_sigelt' env val_decl in
                       (match uu____13234 with | (decls,env) -> (env, decls))
                   | uu____13241 -> (env, [])) env (Prims.snd lbs) in
          (match uu____13198 with
           | (env,decls) -> ((FStar_List.flatten decls), env))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13251,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t;
                          FStar_Syntax_Syntax.lbunivs = uu____13253;
                          FStar_Syntax_Syntax.lbtyp = uu____13254;
                          FStar_Syntax_Syntax.lbeff = uu____13255;
                          FStar_Syntax_Syntax.lbdef = uu____13256;_}::[]),uu____13257,uu____13258,uu____13259,uu____13260)
          when FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid
          ->
          let uu____13276 =
            new_term_constant_and_tok_from_lid env
              (b2t.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13276 with
           | (tname,ttok,env) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let valid_b2t_x =
                 let uu____13294 =
                   let uu____13298 =
                     let uu____13300 =
                       FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
                     [uu____13300] in
                   ("Valid", uu____13298) in
                 FStar_SMTEncoding_Util.mkApp uu____13294 in
               let decls =
                 let uu____13305 =
                   let uu____13307 =
                     let uu____13308 =
                       let uu____13313 =
                         let uu____13314 =
                           let uu____13320 =
                             let uu____13321 =
                               let uu____13324 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13324) in
                             FStar_SMTEncoding_Util.mkEq uu____13321 in
                           ([[valid_b2t_x]], [xx], uu____13320) in
                         FStar_SMTEncoding_Util.mkForall uu____13314 in
                       (uu____13313, (Some "b2t def"), (Some "b2t_def")) in
                     FStar_SMTEncoding_Term.Assume uu____13308 in
                   [uu____13307] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13305 in
               (decls, env))
      | FStar_Syntax_Syntax.Sig_let
          (uu____13342,uu____13343,uu____13344,quals,uu____13346) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___127_13354  ->
                  match uu___127_13354 with
                  | FStar_Syntax_Syntax.Discriminator uu____13355 -> true
                  | uu____13356 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          (uu____13358,uu____13359,lids,quals,uu____13362) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13371 =
                     let uu____13372 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13372.FStar_Ident.idText in
                   uu____13371 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___128_13374  ->
                     match uu___128_13374 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13375 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13378,uu____13379,quals,uu____13381) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___129_13393  ->
                  match uu___129_13393 with
                  | FStar_Syntax_Syntax.Projector uu____13394 -> true
                  | uu____13397 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13404 = try_lookup_free_var env l in
          (match uu____13404 with
           | Some uu____13408 -> ([], env)
           | None  ->
               let se =
                 FStar_Syntax_Syntax.Sig_declare_typ
                   (l, (lb.FStar_Syntax_Syntax.lbunivs),
                     (lb.FStar_Syntax_Syntax.lbtyp), quals,
                     (FStar_Ident.range_of_lid l)) in
               encode_sigelt env se)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13417,uu____13418,quals,uu____13420) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
          ->
          let reify_lb lb =
            let uu____13437 =
              let uu____13438 =
                FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef in
              uu____13438.FStar_Syntax_Syntax.n in
            match uu____13437 with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____13443) ->
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
                  let uu____13500 =
                    FStar_Syntax_Util.arrow_formals_comp
                      lb.FStar_Syntax_Syntax.lbtyp in
                  match uu____13500 with
                  | (formals,comp) ->
                      let reified_typ =
                        FStar_TypeChecker_Env.reify_comp
                          (let uu___155_13517 = env.tcenv in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___155_13517.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___155_13517.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___155_13517.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___155_13517.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___155_13517.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___155_13517.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___155_13517.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___155_13517.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___155_13517.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___155_13517.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___155_13517.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___155_13517.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___155_13517.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___155_13517.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___155_13517.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___155_13517.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___155_13517.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___155_13517.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___155_13517.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.type_of =
                               (uu___155_13517.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___155_13517.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___155_13517.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qname_and_index =
                               (uu___155_13517.FStar_TypeChecker_Env.qname_and_index)
                           }) comp FStar_Syntax_Syntax.U_unknown in
                      let uu____13518 =
                        FStar_Syntax_Syntax.mk_Total reified_typ in
                      FStar_Syntax_Util.arrow formals uu____13518 in
                let lb =
                  let uu___156_13522 = lb in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___156_13522.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___156_13522.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = lb_typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___156_13522.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = tm'
                  } in
                ((let uu____13524 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug env.tcenv)
                      (FStar_Options.Other "SMTEncodingReify") in
                  match uu____13524 with
                  | true  ->
                      let uu____13525 =
                        FStar_Syntax_Print.lbname_to_string
                          lb.FStar_Syntax_Syntax.lbname in
                      let uu____13526 = FStar_Syntax_Print.term_to_string tm in
                      let uu____13527 = FStar_Syntax_Print.term_to_string tm' in
                      FStar_Util.print3 "%s: Reified %s\nto %s\n" uu____13525
                        uu____13526 uu____13527
                  | uu____13528 -> ());
                 lb)
            | uu____13529 ->
                let uu____13530 =
                  let uu____13531 =
                    FStar_Syntax_Print.lbname_to_string
                      lb.FStar_Syntax_Syntax.lbname in
                  FStar_Util.format1
                    "Unable to reify %s at smt encoding. It might be time to have a more robust code for this cases."
                    uu____13531 in
                failwith uu____13530 in
          let uu____13532 =
            let uu____13536 = FStar_List.map reify_lb bindings in
            (is_rec, uu____13536) in
          encode_top_level_let env uu____13532 quals
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13541,uu____13542,quals,uu____13544) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle
          (ses,uu____13558,uu____13559,uu____13560) ->
          let uu____13567 = encode_signature env ses in
          (match uu____13567 with
           | (g,env) ->
               let uu____13577 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___130_13587  ->
                         match uu___130_13587 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13588,Some "inversion axiom",uu____13589)
                             -> false
                         | uu____13593 -> true)) in
               (match uu____13577 with
                | (g',inversions) ->
                    let uu____13602 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___131_13612  ->
                              match uu___131_13612 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13613 ->
                                  true
                              | uu____13619 -> false)) in
                    (match uu____13602 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13630,tps,k,uu____13633,datas,quals,uu____13636) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___132_13645  ->
                    match uu___132_13645 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13646 -> false)) in
          let constructor_or_logic_type_decl c =
            match is_logical with
            | true  ->
                let uu____13669 = c in
                (match uu____13669 with
                 | (name,args,uu____13681,uu____13682,uu____13683) ->
                     let uu____13690 =
                       let uu____13691 =
                         let uu____13697 =
                           FStar_All.pipe_right args
                             (FStar_List.map Prims.snd) in
                         (name, uu____13697,
                           FStar_SMTEncoding_Term.Term_sort, None) in
                       FStar_SMTEncoding_Term.DeclFun uu____13691 in
                     [uu____13690])
            | uu____13707 -> FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13722 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13725 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13725 FStar_Option.isNone)) in
            match uu____13722 with
            | true  -> []
            | uu____13735 ->
                let uu____13736 =
                  fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
                (match uu____13736 with
                 | (xxsym,xx) ->
                     let uu____13742 =
                       FStar_All.pipe_right datas
                         (FStar_List.fold_left
                            (fun uu____13753  ->
                               fun l  ->
                                 match uu____13753 with
                                 | (out,decls) ->
                                     let uu____13765 =
                                       FStar_TypeChecker_Env.lookup_datacon
                                         env.tcenv l in
                                     (match uu____13765 with
                                      | (uu____13771,data_t) ->
                                          let uu____13773 =
                                            FStar_Syntax_Util.arrow_formals
                                              data_t in
                                          (match uu____13773 with
                                           | (args,res) ->
                                               let indices =
                                                 let uu____13802 =
                                                   let uu____13803 =
                                                     FStar_Syntax_Subst.compress
                                                       res in
                                                   uu____13803.FStar_Syntax_Syntax.n in
                                                 match uu____13802 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____13811,indices) ->
                                                     indices
                                                 | uu____13827 -> [] in
                                               let env =
                                                 FStar_All.pipe_right args
                                                   (FStar_List.fold_left
                                                      (fun env  ->
                                                         fun uu____13839  ->
                                                           match uu____13839
                                                           with
                                                           | (x,uu____13843)
                                                               ->
                                                               let uu____13844
                                                                 =
                                                                 let uu____13845
                                                                   =
                                                                   let uu____13849
                                                                    =
                                                                    mk_term_projector_name
                                                                    l x in
                                                                   (uu____13849,
                                                                    [xx]) in
                                                                 FStar_SMTEncoding_Util.mkApp
                                                                   uu____13845 in
                                                               push_term_var
                                                                 env x
                                                                 uu____13844)
                                                      env) in
                                               let uu____13851 =
                                                 encode_args indices env in
                                               (match uu____13851 with
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
                                                      | uu____13869 -> ());
                                                     (let eqs =
                                                        let uu____13871 =
                                                          FStar_List.map2
                                                            (fun v  ->
                                                               fun a  ->
                                                                 let uu____13879
                                                                   =
                                                                   let uu____13882
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v in
                                                                   (uu____13882,
                                                                    a) in
                                                                 FStar_SMTEncoding_Util.mkEq
                                                                   uu____13879)
                                                            vars indices in
                                                        FStar_All.pipe_right
                                                          uu____13871
                                                          FStar_SMTEncoding_Util.mk_and_l in
                                                      let uu____13884 =
                                                        let uu____13885 =
                                                          let uu____13888 =
                                                            let uu____13889 =
                                                              let uu____13892
                                                                =
                                                                mk_data_tester
                                                                  env l xx in
                                                              (uu____13892,
                                                                eqs) in
                                                            FStar_SMTEncoding_Util.mkAnd
                                                              uu____13889 in
                                                          (out, uu____13888) in
                                                        FStar_SMTEncoding_Util.mkOr
                                                          uu____13885 in
                                                      (uu____13884,
                                                        (FStar_List.append
                                                           decls decls'))))))))
                            (FStar_SMTEncoding_Util.mkFalse, [])) in
                     (match uu____13742 with
                      | (data_ax,decls) ->
                          let uu____13900 =
                            fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                          (match uu____13900 with
                           | (ffsym,ff) ->
                               let fuel_guarded_inversion =
                                 let xx_has_type_sfuel =
                                   match (FStar_List.length datas) >
                                           (Prims.parse_int "1")
                                   with
                                   | true  ->
                                       let uu____13911 =
                                         FStar_SMTEncoding_Util.mkApp
                                           ("SFuel", [ff]) in
                                       FStar_SMTEncoding_Term.mk_HasTypeFuel
                                         uu____13911 xx tapp
                                   | uu____13913 ->
                                       FStar_SMTEncoding_Term.mk_HasTypeFuel
                                         ff xx tapp in
                                 let uu____13914 =
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
                                           (xx_has_type_sfuel, data_ax) in
                                       ([[xx_has_type_sfuel]], uu____13926,
                                         uu____13934) in
                                     FStar_SMTEncoding_Util.mkForall
                                       uu____13920 in
                                   let uu____13942 =
                                     let uu____13944 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "fuel_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     Some uu____13944 in
                                   (uu____13919, (Some "inversion axiom"),
                                     uu____13942) in
                                 FStar_SMTEncoding_Term.Assume uu____13914 in
                               let pattern_guarded_inversion =
                                 let uu____13949 =
                                   (contains_name env "Prims.inversion") &&
                                     ((FStar_List.length datas) >
                                        (Prims.parse_int "1")) in
                                 match uu____13949 with
                                 | true  ->
                                     let xx_has_type_fuel =
                                       FStar_SMTEncoding_Term.mk_HasTypeFuel
                                         ff xx tapp in
                                     let pattern_guard =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("Prims.inversion", [tapp]) in
                                     let uu____13957 =
                                       let uu____13958 =
                                         let uu____13963 =
                                           let uu____13964 =
                                             let uu____13970 =
                                               add_fuel
                                                 (ffsym,
                                                   FStar_SMTEncoding_Term.Fuel_sort)
                                                 ((xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 :: vars) in
                                             let uu____13978 =
                                               FStar_SMTEncoding_Util.mkImp
                                                 (xx_has_type_fuel, data_ax) in
                                             ([[xx_has_type_fuel;
                                               pattern_guard]], uu____13970,
                                               uu____13978) in
                                           FStar_SMTEncoding_Util.mkForall
                                             uu____13964 in
                                         let uu____13986 =
                                           let uu____13988 =
                                             varops.mk_unique
                                               (Prims.strcat
                                                  "pattern_guarded_inversion_"
                                                  t.FStar_Ident.str) in
                                           Some uu____13988 in
                                         (uu____13963,
                                           (Some "inversion axiom"),
                                           uu____13986) in
                                       FStar_SMTEncoding_Term.Assume
                                         uu____13958 in
                                     [uu____13957]
                                 | uu____13991 -> [] in
                               FStar_List.append decls
                                 (FStar_List.append [fuel_guarded_inversion]
                                    pattern_guarded_inversion)))) in
          let uu____13992 =
            let uu____14000 =
              let uu____14001 = FStar_Syntax_Subst.compress k in
              uu____14001.FStar_Syntax_Syntax.n in
            match uu____14000 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14030 -> (tps, k) in
          (match uu____13992 with
           | (formals,res) ->
               let uu____14045 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14045 with
                | (formals,res) ->
                    let uu____14052 = encode_binders None formals env in
                    (match uu____14052 with
                     | (vars,guards,env',binder_decls,uu____14067) ->
                         let uu____14074 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14074 with
                          | (tname,ttok,env) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14087 =
                                  let uu____14091 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14091) in
                                FStar_SMTEncoding_Util.mkApp uu____14087 in
                              let uu____14096 =
                                let tname_decl =
                                  let uu____14102 =
                                    let uu____14111 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14123  ->
                                              match uu____14123 with
                                              | (n,s) ->
                                                  ((Prims.strcat tname n), s))) in
                                    let uu____14130 = varops.next_id () in
                                    (tname, uu____14111,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14130, false) in
                                  constructor_or_logic_type_decl uu____14102 in
                                let uu____14134 =
                                  match vars with
                                  | [] ->
                                      let uu____14141 =
                                        let uu____14142 =
                                          let uu____14144 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14144 in
                                        push_free_var env t tname uu____14142 in
                                      ([], uu____14141)
                                  | uu____14148 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14154 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14154 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14163 =
                                          let uu____14168 =
                                            let uu____14169 =
                                              let uu____14177 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14177) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14169 in
                                          (uu____14168,
                                            (Some "name-token correspondence"),
                                            (Some
                                               (Prims.strcat
                                                  "token_correspondence_"
                                                  ttok))) in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____14163 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env) in
                                match uu____14134 with
                                | (tok_decls,env) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env) in
                              (match uu____14096 with
                               | (decls,env) ->
                                   let kindingAx =
                                     let uu____14201 =
                                       encode_term_pred None res env' tapp in
                                     match uu____14201 with
                                     | (k,decls) ->
                                         let karr =
                                           match (FStar_List.length formals)
                                                   > (Prims.parse_int "0")
                                           with
                                           | true  ->
                                               let uu____14215 =
                                                 let uu____14216 =
                                                   let uu____14221 =
                                                     let uu____14222 =
                                                       FStar_SMTEncoding_Term.mk_PreType
                                                         ttok_tm in
                                                     FStar_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu____14222 in
                                                   (uu____14221,
                                                     (Some "kinding"),
                                                     (Some
                                                        (Prims.strcat
                                                           "pre_kinding_"
                                                           ttok))) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____14216 in
                                               [uu____14215]
                                           | uu____14225 -> [] in
                                         let uu____14226 =
                                           let uu____14228 =
                                             let uu____14230 =
                                               let uu____14231 =
                                                 let uu____14236 =
                                                   let uu____14237 =
                                                     let uu____14243 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k) in
                                                     ([[tapp]], vars,
                                                       uu____14243) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14237 in
                                                 (uu____14236, None,
                                                   (Some
                                                      (Prims.strcat
                                                         "kinding_" ttok))) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14231 in
                                             [uu____14230] in
                                           FStar_List.append karr uu____14228 in
                                         FStar_List.append decls uu____14226 in
                                   let aux =
                                     let uu____14253 =
                                       let uu____14255 =
                                         inversion_axioms tapp vars in
                                       let uu____14257 =
                                         let uu____14259 =
                                           pretype_axiom tapp vars in
                                         [uu____14259] in
                                       FStar_List.append uu____14255
                                         uu____14257 in
                                     FStar_List.append kindingAx uu____14253 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14264,uu____14265,uu____14266,uu____14267,uu____14268,uu____14269,uu____14270)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14277,t,uu____14279,n_tps,quals,uu____14282,drange) ->
          let uu____14288 = new_term_constant_and_tok_from_lid env d in
          (match uu____14288 with
           | (ddconstrsym,ddtok,env) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14299 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14299 with
                | (formals,t_res) ->
                    let uu____14321 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14321 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14330 =
                           encode_binders (Some fuel_tm) formals env in
                         (match uu____14330 with
                          | (vars,guards,env',binder_decls,names) ->
                              let projectors =
                                FStar_All.pipe_right names
                                  (FStar_List.map
                                     (fun x  ->
                                        let uu____14363 =
                                          mk_term_projector_name d x in
                                        (uu____14363,
                                          FStar_SMTEncoding_Term.Term_sort))) in
                              let datacons =
                                let uu____14365 =
                                  let uu____14374 = varops.next_id () in
                                  (ddconstrsym, projectors,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14374, true) in
                                FStar_All.pipe_right uu____14365
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
                              let uu____14394 =
                                encode_term_pred None t env ddtok_tm in
                              (match uu____14394 with
                               | (tok_typing,decls3) ->
                                   let uu____14401 =
                                     encode_binders (Some fuel_tm) formals
                                       env in
                                   (match uu____14401 with
                                    | (vars',guards',env'',decls_formals,uu____14416)
                                        ->
                                        let uu____14423 =
                                          let xvars =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp in
                                        (match uu____14423 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14442 ->
                                                   let uu____14446 =
                                                     let uu____14447 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14447 in
                                                   [uu____14446] in
                                             let encode_elim uu____14454 =
                                               let uu____14455 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14455 with
                                               | (head,args) ->
                                                   let uu____14484 =
                                                     let uu____14485 =
                                                       FStar_Syntax_Subst.compress
                                                         head in
                                                     uu____14485.FStar_Syntax_Syntax.n in
                                                   (match uu____14484 with
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
                                                        let uu____14503 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14503
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let uu____14514
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14525
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14525
                                                                    with
                                                                    | 
                                                                    (env,arg_vars,eqns)
                                                                    ->
                                                                    let uu____14544
                                                                    =
                                                                    let uu____14548
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env
                                                                    uu____14548 in
                                                                    (match uu____14544
                                                                    with
                                                                    | 
                                                                    (uu____14554,xv,env)
                                                                    ->
                                                                    let uu____14557
                                                                    =
                                                                    let uu____14559
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14559
                                                                    :: eqns in
                                                                    (env, (xv
                                                                    ::
                                                                    arg_vars),
                                                                    uu____14557)))
                                                                 (env', [],
                                                                   [])
                                                                 encoded_args in
                                                             (match uu____14514
                                                              with
                                                              | (uu____14567,arg_vars,eqns)
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
                                                                    let uu____14588
                                                                    =
                                                                    let uu____14593
                                                                    =
                                                                    let uu____14594
                                                                    =
                                                                    let uu____14600
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14606
                                                                    =
                                                                    let uu____14607
                                                                    =
                                                                    let uu____14610
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    eqns
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14610) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14607 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14600,
                                                                    uu____14606) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14594 in
                                                                    (uu____14593,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14588 in
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
                                                                    let uu____14624
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14624,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14626
                                                                    =
                                                                    let uu____14631
                                                                    =
                                                                    let uu____14632
                                                                    =
                                                                    let uu____14638
                                                                    =
                                                                    let uu____14641
                                                                    =
                                                                    let uu____14643
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp in
                                                                    [uu____14643] in
                                                                    [uu____14641] in
                                                                    let uu____14646
                                                                    =
                                                                    let uu____14647
                                                                    =
                                                                    let uu____14650
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14651
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp in
                                                                    (uu____14650,
                                                                    uu____14651) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14647 in
                                                                    (uu____14638,
                                                                    [x],
                                                                    uu____14646) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14632 in
                                                                    let uu____14661
                                                                    =
                                                                    let uu____14663
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    Some
                                                                    uu____14663 in
                                                                    (uu____14631,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14661) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14626
                                                                    | 
                                                                    uu____14666
                                                                    ->
                                                                    let prec
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.collect
                                                                    (fun v 
                                                                    ->
                                                                    match 
                                                                    Prims.snd
                                                                    v
                                                                    with
                                                                    | 
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                     -> []
                                                                    | 
                                                                    FStar_SMTEncoding_Term.Term_sort
                                                                     ->
                                                                    let uu____14677
                                                                    =
                                                                    let uu____14678
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14678
                                                                    dapp in
                                                                    [uu____14677]
                                                                    | 
                                                                    uu____14679
                                                                    ->
                                                                    failwith
                                                                    "unexpected sort")) in
                                                                    let uu____14681
                                                                    =
                                                                    let uu____14686
                                                                    =
                                                                    let uu____14687
                                                                    =
                                                                    let uu____14693
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14699
                                                                    =
                                                                    let uu____14700
                                                                    =
                                                                    let uu____14703
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14703) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14700 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14693,
                                                                    uu____14699) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14687 in
                                                                    (uu____14686,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14681 in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14714 ->
                                                        ((let uu____14716 =
                                                            let uu____14717 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14718 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14717
                                                              uu____14718 in
                                                          FStar_Errors.warn
                                                            drange
                                                            uu____14716);
                                                         ([], []))) in
                                             let uu____14721 = encode_elim () in
                                             (match uu____14721 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14733 =
                                                      let uu____14735 =
                                                        let uu____14737 =
                                                          let uu____14739 =
                                                            let uu____14741 =
                                                              let uu____14742
                                                                =
                                                                let uu____14748
                                                                  =
                                                                  let uu____14750
                                                                    =
                                                                    let uu____14751
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14751 in
                                                                  Some
                                                                    uu____14750 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14748) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14742 in
                                                            [uu____14741] in
                                                          let uu____14754 =
                                                            let uu____14756 =
                                                              let uu____14758
                                                                =
                                                                let uu____14760
                                                                  =
                                                                  let uu____14762
                                                                    =
                                                                    let uu____14764
                                                                    =
                                                                    let uu____14766
                                                                    =
                                                                    let uu____14767
                                                                    =
                                                                    let uu____14772
                                                                    =
                                                                    let uu____14773
                                                                    =
                                                                    let uu____14779
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14779) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14773 in
                                                                    (uu____14772,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14767 in
                                                                    let uu____14787
                                                                    =
                                                                    let uu____14789
                                                                    =
                                                                    let uu____14790
                                                                    =
                                                                    let uu____14795
                                                                    =
                                                                    let uu____14796
                                                                    =
                                                                    let uu____14802
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14808
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14802,
                                                                    uu____14808) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14796 in
                                                                    (uu____14795,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14790 in
                                                                    [uu____14789] in
                                                                    uu____14766
                                                                    ::
                                                                    uu____14787 in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))))
                                                                    ::
                                                                    uu____14764 in
                                                                  FStar_List.append
                                                                    uu____14762
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14760 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14758 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14756 in
                                                          FStar_List.append
                                                            uu____14739
                                                            uu____14754 in
                                                        FStar_List.append
                                                          decls3 uu____14737 in
                                                      FStar_List.append
                                                        decls2 uu____14735 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14733 in
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
           (fun uu____14831  ->
              fun se  ->
                match uu____14831 with
                | (g,env) ->
                    let uu____14843 = encode_sigelt env se in
                    (match uu____14843 with
                     | (g',env) -> ((FStar_List.append g g'), env)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14879 =
        match uu____14879 with
        | (i,decls,env) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14897 ->
                 ((i + (Prims.parse_int "1")), [], env)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14902 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   match uu____14902 with
                   | true  ->
                       let uu____14903 = FStar_Syntax_Print.bv_to_string x in
                       let uu____14904 =
                         FStar_Syntax_Print.term_to_string
                           x.FStar_Syntax_Syntax.sort in
                       let uu____14905 = FStar_Syntax_Print.term_to_string t1 in
                       FStar_Util.print3 "Normalized %s : %s to %s\n"
                         uu____14903 uu____14904 uu____14905
                   | uu____14906 -> ());
                  (let uu____14907 = encode_term t1 env in
                   match uu____14907 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14917 =
                         let uu____14921 =
                           let uu____14922 =
                             let uu____14923 =
                               FStar_Util.digest_of_string t_hash in
                             let uu____14924 =
                               let uu____14925 = FStar_Util.string_of_int i in
                               Prims.strcat "_" uu____14925 in
                             Prims.strcat uu____14923 uu____14924 in
                           Prims.strcat "x_" uu____14922 in
                         new_term_constant_from_string env x uu____14921 in
                       (match uu____14917 with
                        | (xxsym,xx,env') ->
                            let t =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____14936 = FStar_Options.log_queries () in
                              match uu____14936 with
                              | true  ->
                                  let uu____14938 =
                                    let uu____14939 =
                                      FStar_Syntax_Print.bv_to_string x in
                                    let uu____14940 =
                                      FStar_Syntax_Print.term_to_string
                                        x.FStar_Syntax_Syntax.sort in
                                    let uu____14941 =
                                      FStar_Syntax_Print.term_to_string t1 in
                                    FStar_Util.format3 "%s : %s (%s)"
                                      uu____14939 uu____14940 uu____14941 in
                                  Some uu____14938
                              | uu____14942 -> None in
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14954,t)) ->
                 let t_norm = whnf env t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____14963 = encode_free_var env fv t t_norm [] in
                 (match uu____14963 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____14982 = encode_sigelt env se in
                 (match uu____14982 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____14992 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____14992 with | (uu____15004,decls,env) -> (decls, env)
let encode_labels labs =
  let prefix =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15049  ->
            match uu____15049 with
            | (l,uu____15056,uu____15057) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15078  ->
            match uu____15078 with
            | (l,uu____15086,uu____15087) ->
                let uu____15092 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____15093 =
                  let uu____15095 =
                    let uu____15096 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15096 in
                  [uu____15095] in
                uu____15092 :: uu____15093)) in
  (prefix, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15107 =
      let uu____15109 =
        let uu____15110 = FStar_Util.smap_create (Prims.parse_int "100") in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15110;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true
        } in
      [uu____15109] in
    FStar_ST.write last_env uu____15107
let get_env: FStar_TypeChecker_Env.env -> env_t =
  fun tcenv  ->
    let uu____15128 = FStar_ST.read last_env in
    match uu____15128 with
    | [] -> failwith "No env; call init first!"
    | e::uu____15134 ->
        let uu___157_15136 = e in
        {
          bindings = (uu___157_15136.bindings);
          depth = (uu___157_15136.depth);
          tcenv;
          warn = (uu___157_15136.warn);
          cache = (uu___157_15136.cache);
          nolabels = (uu___157_15136.nolabels);
          use_zfuel_name = (uu___157_15136.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___157_15136.encode_non_total_function_typ)
        }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15140 = FStar_ST.read last_env in
    match uu____15140 with
    | [] -> failwith "Empty env stack"
    | uu____15145::tl -> FStar_ST.write last_env (env :: tl)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15153  ->
    let uu____15154 = FStar_ST.read last_env in
    match uu____15154 with
    | [] -> failwith "Empty env stack"
    | hd::tl ->
        let refs = FStar_Util.smap_copy hd.cache in
        let top =
          let uu___158_15175 = hd in
          {
            bindings = (uu___158_15175.bindings);
            depth = (uu___158_15175.depth);
            tcenv = (uu___158_15175.tcenv);
            warn = (uu___158_15175.warn);
            cache = refs;
            nolabels = (uu___158_15175.nolabels);
            use_zfuel_name = (uu___158_15175.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___158_15175.encode_non_total_function_typ)
          } in
        FStar_ST.write last_env (top :: hd :: tl)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15181  ->
    let uu____15182 = FStar_ST.read last_env in
    match uu____15182 with
    | [] -> failwith "Popping an empty stack"
    | uu____15187::tl -> FStar_ST.write last_env tl
let mark_env: Prims.unit -> Prims.unit = fun uu____15195  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15198  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15201  ->
    let uu____15202 = FStar_ST.read last_env in
    match uu____15202 with
    | hd::uu____15208::tl -> FStar_ST.write last_env (hd :: tl)
    | uu____15214 -> failwith "Impossible"
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
        let uu____15259 = FStar_Options.log_queries () in
        match uu____15259 with
        | true  ->
            let uu____15261 =
              let uu____15262 =
                let uu____15263 =
                  let uu____15264 =
                    FStar_All.pipe_right
                      (FStar_Syntax_Util.lids_of_sigelt se)
                      (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                  FStar_All.pipe_right uu____15264 (FStar_String.concat ", ") in
                Prims.strcat "encoding sigelt " uu____15263 in
              FStar_SMTEncoding_Term.Caption uu____15262 in
            uu____15261 :: decls
        | uu____15269 -> decls in
      let env = get_env tcenv in
      let uu____15271 = encode_sigelt env se in
      match uu____15271 with
      | (decls,env) ->
          (set_env env;
           (let uu____15277 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15277))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (match modul.FStar_Syntax_Syntax.is_interface with
           | true  -> "interface"
           | uu____15286 -> "module")
          (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15288 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       match uu____15288 with
       | true  ->
           let uu____15289 =
             FStar_All.pipe_right
               (FStar_List.length modul.FStar_Syntax_Syntax.exports)
               FStar_Util.string_of_int in
           FStar_Util.print2
             "+++++++++++Encoding externals for %s ... %s exports\n" name
             uu____15289
       | uu____15292 -> ());
      (let env = get_env tcenv in
       let uu____15294 =
         encode_signature
           (let uu___159_15298 = env in
            {
              bindings = (uu___159_15298.bindings);
              depth = (uu___159_15298.depth);
              tcenv = (uu___159_15298.tcenv);
              warn = false;
              cache = (uu___159_15298.cache);
              nolabels = (uu___159_15298.nolabels);
              use_zfuel_name = (uu___159_15298.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___159_15298.encode_non_total_function_typ)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15294 with
       | (decls,env) ->
           let caption decls =
             let uu____15310 = FStar_Options.log_queries () in
             match uu____15310 with
             | true  ->
                 let msg = Prims.strcat "Externals for " name in
                 FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                   decls)
                   [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             | uu____15313 -> decls in
           (set_env
              (let uu___160_15315 = env in
               {
                 bindings = (uu___160_15315.bindings);
                 depth = (uu___160_15315.depth);
                 tcenv = (uu___160_15315.tcenv);
                 warn = true;
                 cache = (uu___160_15315.cache);
                 nolabels = (uu___160_15315.nolabels);
                 use_zfuel_name = (uu___160_15315.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___160_15315.encode_non_total_function_typ)
               });
            (let uu____15317 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             match uu____15317 with
             | true  ->
                 FStar_Util.print1 "Done encoding externals for %s\n" name
             | uu____15318 -> ());
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
        (let uu____15352 =
           let uu____15353 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15353.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15352);
        (let env = get_env tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15361 =
           let rec aux bindings =
             match bindings with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15382 = aux rest in
                 (match uu____15382 with
                  | (out,rest) ->
                      let t =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv x.FStar_Syntax_Syntax.sort in
                      let uu____15398 =
                        let uu____15400 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___161_15401 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___161_15401.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___161_15401.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t
                             }) in
                        uu____15400 :: out in
                      (uu____15398, rest))
             | uu____15404 -> ([], bindings) in
           let uu____15408 = aux bindings in
           match uu____15408 with
           | (closing,bindings) ->
               let uu____15422 =
                 FStar_Syntax_Util.close_forall (FStar_List.rev closing) q in
               (uu____15422, bindings) in
         match uu____15361 with
         | (q,bindings) ->
             let uu____15435 =
               let uu____15438 =
                 FStar_List.filter
                   (fun uu___133_15440  ->
                      match uu___133_15440 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15441 ->
                          false
                      | uu____15445 -> true) bindings in
               encode_env_bindings env uu____15438 in
             (match uu____15435 with
              | (env_decls,env) ->
                  ((let uu____15456 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    match uu____15456 with
                    | true  ->
                        let uu____15457 = FStar_Syntax_Print.term_to_string q in
                        FStar_Util.print1 "Encoding query formula: %s\n"
                          uu____15457
                    | uu____15458 -> ());
                   (let uu____15459 = encode_formula q env in
                    match uu____15459 with
                    | (phi,qdecls) ->
                        let uu____15471 =
                          let uu____15474 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15474 phi in
                        (match uu____15471 with
                         | (labels,phi) ->
                             let uu____15484 = encode_labels labels in
                             (match uu____15484 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15505 =
                                      let uu____15510 =
                                        FStar_SMTEncoding_Util.mkNot phi in
                                      let uu____15511 =
                                        let uu____15513 =
                                          varops.mk_unique "@query" in
                                        Some uu____15513 in
                                      (uu____15510, (Some "query"),
                                        uu____15511) in
                                    FStar_SMTEncoding_Term.Assume uu____15505 in
                                  let suffix =
                                    let uu____15518 =
                                      let uu____15520 =
                                        let uu____15522 =
                                          FStar_Options.print_z3_statistics
                                            () in
                                        match uu____15522 with
                                        | true  ->
                                            [FStar_SMTEncoding_Term.PrintStats]
                                        | uu____15524 -> [] in
                                      FStar_List.append uu____15520
                                        [FStar_SMTEncoding_Term.Echo "Done!"] in
                                    FStar_List.append label_suffix
                                      uu____15518 in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env = get_env tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15535 = encode_formula q env in
       match uu____15535 with
       | (f,uu____15539) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15541) -> true
             | uu____15544 -> false)))