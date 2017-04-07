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
            let uu____121 =
              let uu____122 = FStar_Syntax_Syntax.get_lazy_comp l1 in
              uu____122 () in
            FStar_Syntax_Subst.subst_comp s uu____121 in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____118 in
        FStar_Util.Inl uu____117 in
      Some uu____114
  | uu____129 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_'
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___135_143 = a in
        let uu____144 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____144;
          FStar_Syntax_Syntax.index =
            (uu___135_143.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___135_143.FStar_Syntax_Syntax.sort)
        } in
      let uu____145 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____145
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____158 =
          let uu____159 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____159 in
        let uu____160 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____160 with
        | (uu____163,t) ->
            let uu____165 =
              let uu____166 = FStar_Syntax_Subst.compress t in
              uu____166.FStar_Syntax_Syntax.n in
            (match uu____165 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____181 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____181 with
                  | (binders,uu____185) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid (Prims.fst b)))
             | uu____196 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____203 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____203
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____210 =
        let uu____213 = mk_term_projector_name lid a in
        (uu____213,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____210
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____220 =
        let uu____223 = mk_term_projector_name_by_pos lid i in
        (uu____223,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____220
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
  let new_scope uu____413 =
    let uu____414 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____416 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____414, uu____416) in
  let scopes =
    let uu____427 = let uu____433 = new_scope () in [uu____433] in
    FStar_Util.mk_ref uu____427 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____458 =
        let uu____460 = FStar_ST.read scopes in
        FStar_Util.find_map uu____460
          (fun uu____477  ->
             match uu____477 with
             | (names1,uu____484) -> FStar_Util.smap_try_find names1 y1) in
      match uu____458 with
      | None  -> y1
      | Some uu____489 ->
          (FStar_Util.incr ctr;
           (let uu____494 =
              let uu____495 =
                let uu____496 = FStar_ST.read ctr in
                Prims.string_of_int uu____496 in
              Prims.strcat "__" uu____495 in
            Prims.strcat y1 uu____494)) in
    let top_scope =
      let uu____501 =
        let uu____506 = FStar_ST.read scopes in FStar_List.hd uu____506 in
      FStar_All.pipe_left Prims.fst uu____501 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____545 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____556 =
      let uu____557 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____557 in
    FStar_Util.format2 "%s_%s" pfx uu____556 in
  let string_const s =
    let uu____562 =
      let uu____564 = FStar_ST.read scopes in
      FStar_Util.find_map uu____564
        (fun uu____581  ->
           match uu____581 with
           | (uu____587,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____562 with
    | Some f -> f
    | None  ->
        let id = next_id1 () in
        let f =
          let uu____596 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____596 in
        let top_scope =
          let uu____599 =
            let uu____604 = FStar_ST.read scopes in FStar_List.hd uu____604 in
          FStar_All.pipe_left Prims.snd uu____599 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____632 =
    let uu____633 =
      let uu____639 = new_scope () in
      let uu____644 = FStar_ST.read scopes in uu____639 :: uu____644 in
    FStar_ST.write scopes uu____633 in
  let pop1 uu____671 =
    let uu____672 =
      let uu____678 = FStar_ST.read scopes in FStar_List.tl uu____678 in
    FStar_ST.write scopes uu____672 in
  let mark1 uu____705 = push1 () in
  let reset_mark1 uu____709 = pop1 () in
  let commit_mark1 uu____713 =
    let uu____714 = FStar_ST.read scopes in
    match uu____714 with
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
    | uu____774 -> failwith "Impossible" in
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
    let uu___136_783 = x in
    let uu____784 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____784;
      FStar_Syntax_Syntax.index = (uu___136_783.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___136_783.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term Prims.option* FStar_SMTEncoding_Term.term
  Prims.option)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____805 -> false
let __proj__Binding_var__item___0:
  binding -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____829 -> false
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
    let uu____948 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___112_952  ->
              match uu___112_952 with
              | Binding_var (x,uu____954) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____956,uu____957,uu____958) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____948 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option
  =
  fun env  ->
    fun t  ->
      let uu____991 = FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____991
      then
        let uu____993 = FStar_Syntax_Print.term_to_string t in Some uu____993
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1004 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1004)
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
        (let uu___137_1016 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___137_1016.tcenv);
           warn = (uu___137_1016.warn);
           cache = (uu___137_1016.cache);
           nolabels = (uu___137_1016.nolabels);
           use_zfuel_name = (uu___137_1016.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___137_1016.encode_non_total_function_typ)
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
        (let uu___138_1029 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___138_1029.depth);
           tcenv = (uu___138_1029.tcenv);
           warn = (uu___138_1029.warn);
           cache = (uu___138_1029.cache);
           nolabels = (uu___138_1029.nolabels);
           use_zfuel_name = (uu___138_1029.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___138_1029.encode_non_total_function_typ)
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
          (let uu___139_1045 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___139_1045.depth);
             tcenv = (uu___139_1045.tcenv);
             warn = (uu___139_1045.warn);
             cache = (uu___139_1045.cache);
             nolabels = (uu___139_1045.nolabels);
             use_zfuel_name = (uu___139_1045.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___139_1045.encode_non_total_function_typ)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___140_1055 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___140_1055.depth);
          tcenv = (uu___140_1055.tcenv);
          warn = (uu___140_1055.warn);
          cache = (uu___140_1055.cache);
          nolabels = (uu___140_1055.nolabels);
          use_zfuel_name = (uu___140_1055.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___140_1055.encode_non_total_function_typ)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___113_1071  ->
             match uu___113_1071 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1079 -> None) in
      let uu____1082 = aux a in
      match uu____1082 with
      | None  ->
          let a2 = unmangle a in
          let uu____1089 = aux a2 in
          (match uu____1089 with
           | None  ->
               let uu____1095 =
                 let uu____1096 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1097 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1096 uu____1097 in
               failwith uu____1095
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1117 =
        let uu___141_1118 = env in
        let uu____1119 =
          let uu____1121 =
            let uu____1122 =
              let uu____1129 =
                let uu____1131 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1131 in
              (x, fname, uu____1129, None) in
            Binding_fvar uu____1122 in
          uu____1121 :: (env.bindings) in
        {
          bindings = uu____1119;
          depth = (uu___141_1118.depth);
          tcenv = (uu___141_1118.tcenv);
          warn = (uu___141_1118.warn);
          cache = (uu___141_1118.cache);
          nolabels = (uu___141_1118.nolabels);
          use_zfuel_name = (uu___141_1118.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___141_1118.encode_non_total_function_typ)
        } in
      (fname, ftok, uu____1117)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___114_1153  ->
           match uu___114_1153 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1175 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1187 =
        lookup_binding env
          (fun uu___115_1189  ->
             match uu___115_1189 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1199 -> None) in
      FStar_All.pipe_right uu____1187 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1212 = try_lookup_lid env a in
      match uu____1212 with
      | None  ->
          let uu____1229 =
            let uu____1230 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1230 in
          failwith uu____1229
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
          let uu___142_1261 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___142_1261.depth);
            tcenv = (uu___142_1261.tcenv);
            warn = (uu___142_1261.warn);
            cache = (uu___142_1261.cache);
            nolabels = (uu___142_1261.nolabels);
            use_zfuel_name = (uu___142_1261.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___142_1261.encode_non_total_function_typ)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1273 = lookup_lid env x in
        match uu____1273 with
        | (t1,t2,uu____1281) ->
            let t3 =
              let uu____1287 =
                let uu____1291 =
                  let uu____1293 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1293] in
                (f, uu____1291) in
              FStar_SMTEncoding_Util.mkApp uu____1287 in
            let uu___143_1296 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___143_1296.depth);
              tcenv = (uu___143_1296.tcenv);
              warn = (uu___143_1296.warn);
              cache = (uu___143_1296.cache);
              nolabels = (uu___143_1296.nolabels);
              use_zfuel_name = (uu___143_1296.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___143_1296.encode_non_total_function_typ)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1306 = try_lookup_lid env l in
      match uu____1306 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1333 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1338,fuel::[]) ->
                         let uu____1341 =
                           let uu____1342 =
                             let uu____1343 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1343 Prims.fst in
                           FStar_Util.starts_with uu____1342 "fuel" in
                         if uu____1341
                         then
                           let uu____1345 =
                             let uu____1346 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1346
                               fuel in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1345
                         else Some t
                     | uu____1349 -> Some t)
                | uu____1350 -> None))
let lookup_free_var env a =
  let uu____1368 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1368 with
  | Some t -> t
  | None  ->
      let uu____1371 =
        let uu____1372 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1372 in
      failwith uu____1371
let lookup_free_var_name env a =
  let uu____1389 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1389 with | (x,uu____1396,uu____1397) -> x
let lookup_free_var_sym env a =
  let uu____1421 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1421 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1442;
             FStar_SMTEncoding_Term.rng = uu____1443;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1451 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1465 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___116_1474  ->
           match uu___116_1474 with
           | Binding_fvar (uu____1476,nm',tok,uu____1479) when nm = nm' ->
               tok
           | uu____1484 -> None)
let mkForall_fuel' n1 uu____1501 =
  match uu____1501 with
  | (pats,vars,body) ->
      let fallback uu____1517 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1520 = FStar_Options.unthrottle_inductives () in
      if uu____1520
      then fallback ()
      else
        (let uu____1522 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1522 with
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
                       | uu____1541 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1555 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1555
                     | uu____1557 ->
                         let uu____1558 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1558 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1561 -> body in
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
          let uu____1605 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1605 FStar_Option.isNone
      | uu____1618 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1625 =
        let uu____1626 = FStar_Syntax_Util.un_uinst t in
        uu____1626.FStar_Syntax_Syntax.n in
      match uu____1625 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1629,uu____1630,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___117_1659  ->
                  match uu___117_1659 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1660 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1661,uu____1662,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1689 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1689 FStar_Option.isSome
      | uu____1702 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1709 = head_normal env t in
      if uu____1709
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
    let uu____1720 =
      let uu____1724 = FStar_Syntax_Syntax.null_binder t in [uu____1724] in
    let uu____1725 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1720 uu____1725 None
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
                    let uu____1752 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1752
                | s ->
                    let uu____1755 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1755) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___118_1767  ->
    match uu___118_1767 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1768 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____1796;
                       FStar_SMTEncoding_Term.rng = uu____1797;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              aux f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1811) ->
              let uu____1816 =
                ((FStar_List.length args) = (FStar_List.length vars)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1826 -> false) args vars) in
              if uu____1816 then tok_of_name env f else None
          | (uu____1829,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t1 in
              let uu____1832 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1834 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1834)) in
              if uu____1832 then Some t1 else None
          | uu____1837 -> None in
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
           let uu____2497 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2497 with
            | (binders1,res) ->
                let uu____2504 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2504
                then
                  let uu____2507 = encode_binders None binders1 env in
                  (match uu____2507 with
                   | (vars,guards,env',decls,uu____2522) ->
                       let fsym =
                         let uu____2532 = varops.fresh "f" in
                         (uu____2532, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2535 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___144_2539 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___144_2539.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___144_2539.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___144_2539.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___144_2539.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___144_2539.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___144_2539.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___144_2539.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___144_2539.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___144_2539.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___144_2539.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___144_2539.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___144_2539.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___144_2539.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___144_2539.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___144_2539.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___144_2539.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___144_2539.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___144_2539.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___144_2539.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___144_2539.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___144_2539.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___144_2539.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___144_2539.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2535 with
                        | (pre_opt,res_t) ->
                            let uu____2546 =
                              encode_term_pred None res_t env' app in
                            (match uu____2546 with
                             | (res_pred,decls') ->
                                 let uu____2553 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2560 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2560, [])
                                   | Some pre ->
                                       let uu____2563 =
                                         encode_formula pre env' in
                                       (match uu____2563 with
                                        | (guard,decls0) ->
                                            let uu____2571 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2571, decls0)) in
                                 (match uu____2553 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2579 =
                                          let uu____2585 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2585) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2579 in
                                      let cvars =
                                        let uu____2595 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2595
                                          (FStar_List.filter
                                             (fun uu____2601  ->
                                                match uu____2601 with
                                                | (x,uu____2605) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2616 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2616 with
                                       | Some (t',sorts,uu____2632) ->
                                           let uu____2642 =
                                             let uu____2643 =
                                               let uu____2647 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               (t', uu____2647) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2643 in
                                           (uu____2642, [])
                                       | None  ->
                                           let tsym =
                                             let uu____2663 =
                                               let uu____2664 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2664 in
                                             varops.mk_unique uu____2663 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2671 =
                                               FStar_Options.log_queries () in
                                             if uu____2671
                                             then
                                               let uu____2673 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2673
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2679 =
                                               let uu____2683 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2683) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2679 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____2691 =
                                               let uu____2695 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2695, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2691 in
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
                                             let uu____2708 =
                                               let uu____2712 =
                                                 let uu____2713 =
                                                   let uu____2719 =
                                                     let uu____2720 =
                                                       let uu____2723 =
                                                         let uu____2724 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2724 in
                                                       (f_has_t, uu____2723) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2720 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2719) in
                                                 mkForall_fuel uu____2713 in
                                               (uu____2712,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2708 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____2737 =
                                               let uu____2741 =
                                                 let uu____2742 =
                                                   let uu____2748 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2748) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2742 in
                                               (uu____2741, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2737 in
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
                     let uu____2779 =
                       let uu____2783 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____2783, (Some "Typing for non-total arrows"),
                         a_name) in
                     FStar_SMTEncoding_Term.Assume uu____2779 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____2792 =
                       let uu____2796 =
                         let uu____2797 =
                           let uu____2803 =
                             let uu____2804 =
                               let uu____2807 =
                                 let uu____2808 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2808 in
                               (f_has_t, uu____2807) in
                             FStar_SMTEncoding_Util.mkImp uu____2804 in
                           ([[f_has_t]], [fsym], uu____2803) in
                         mkForall_fuel uu____2797 in
                       (uu____2796, (Some a_name), a_name) in
                     FStar_SMTEncoding_Term.Assume uu____2792 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2822 ->
           let uu____2827 =
             let uu____2830 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2830 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2835;
                 FStar_Syntax_Syntax.pos = uu____2836;
                 FStar_Syntax_Syntax.vars = uu____2837;_} ->
                 let uu____2844 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2844 with
                  | (b,f1) ->
                      let uu____2858 =
                        let uu____2859 = FStar_List.hd b in
                        Prims.fst uu____2859 in
                      (uu____2858, f1))
             | uu____2864 -> failwith "impossible" in
           (match uu____2827 with
            | (x,f) ->
                let uu____2871 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____2871 with
                 | (base_t,decls) ->
                     let uu____2878 = gen_term_var env x in
                     (match uu____2878 with
                      | (x1,xtm,env') ->
                          let uu____2887 = encode_formula f env' in
                          (match uu____2887 with
                           | (refinement,decls') ->
                               let uu____2894 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____2894 with
                                | (fsym,fterm) ->
                                    let encoding =
                                      let uu____2902 =
                                        let uu____2905 =
                                          FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                            (Some fterm) xtm base_t in
                                        (uu____2905, refinement) in
                                      FStar_SMTEncoding_Util.mkAnd uu____2902 in
                                    let cvars =
                                      let uu____2910 =
                                        FStar_SMTEncoding_Term.free_variables
                                          encoding in
                                      FStar_All.pipe_right uu____2910
                                        (FStar_List.filter
                                           (fun uu____2916  ->
                                              match uu____2916 with
                                              | (y,uu____2920) ->
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
                                    let uu____2939 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2939 with
                                     | Some (t1,uu____2954,uu____2955) ->
                                         let uu____2965 =
                                           let uu____2966 =
                                             let uu____2970 =
                                               FStar_All.pipe_right cvars
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             (t1, uu____2970) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2966 in
                                         (uu____2965, [])
                                     | None  ->
                                         let tsym =
                                           let uu____2986 =
                                             let uu____2987 =
                                               FStar_Util.digest_of_string
                                                 tkey_hash in
                                             Prims.strcat "Tm_refine_"
                                               uu____2987 in
                                           varops.mk_unique uu____2986 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____2996 =
                                             let uu____3000 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars in
                                             (tsym, uu____3000) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2996 in
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
                                           let uu____3010 =
                                             let uu____3014 =
                                               let uu____3015 =
                                                 let uu____3021 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars,
                                                   uu____3021) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3015 in
                                             (uu____3014,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3010 in
                                         let t_kinding =
                                           let uu____3031 =
                                             let uu____3035 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars,
                                                   t_has_kind) in
                                             (uu____3035,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3031 in
                                         let t_interp =
                                           let uu____3045 =
                                             let uu____3049 =
                                               let uu____3050 =
                                                 let uu____3056 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars), uu____3056) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3050 in
                                             let uu____3068 =
                                               let uu____3070 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3070 in
                                             (uu____3049, uu____3068,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3045 in
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
             let uu____3098 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3098 in
           let uu____3102 = encode_term_pred None k env ttm in
           (match uu____3102 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3110 =
                    let uu____3114 =
                      let uu____3115 =
                        let uu____3116 =
                          let uu____3117 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3117 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3116 in
                      varops.mk_unique uu____3115 in
                    (t_has_k, (Some "Uvar typing"), uu____3114) in
                  FStar_SMTEncoding_Term.Assume uu____3110 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3123 ->
           let uu____3133 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3133 with
            | (head1,args_e) ->
                let uu____3161 =
                  let uu____3169 =
                    let uu____3170 = FStar_Syntax_Subst.compress head1 in
                    uu____3170.FStar_Syntax_Syntax.n in
                  (uu____3169, args_e) in
                (match uu____3161 with
                 | (uu____3180,uu____3181) when head_redex env head1 ->
                     let uu____3192 = whnf env t in
                     encode_term uu____3192 env
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
                     let uu____3266 = encode_term v1 env in
                     (match uu____3266 with
                      | (v11,decls1) ->
                          let uu____3273 = encode_term v2 env in
                          (match uu____3273 with
                           | (v21,decls2) ->
                               let uu____3280 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3280,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3282) ->
                     let e0 =
                       let uu____3296 =
                         let uu____3299 =
                           let uu____3300 =
                             let uu____3310 =
                               let uu____3316 = FStar_List.hd args_e in
                               [uu____3316] in
                             (head1, uu____3310) in
                           FStar_Syntax_Syntax.Tm_app uu____3300 in
                         FStar_Syntax_Syntax.mk uu____3299 in
                       uu____3296 None head1.FStar_Syntax_Syntax.pos in
                     ((let uu____3349 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3349
                       then
                         let uu____3350 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Trying to normalize %s\n"
                           uu____3350
                       else ());
                      (let e01 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Reify;
                           FStar_TypeChecker_Normalize.Eager_unfolding;
                           FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                           env.tcenv e0 in
                       (let uu____3354 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify") in
                        if uu____3354
                        then
                          let uu____3355 =
                            FStar_Syntax_Print.term_to_string e01 in
                          FStar_Util.print1 "Result of normalization %s\n"
                            uu____3355
                        else ());
                       (let e02 =
                          let uu____3358 =
                            let uu____3359 =
                              let uu____3360 =
                                FStar_Syntax_Subst.compress e01 in
                              uu____3360.FStar_Syntax_Syntax.n in
                            match uu____3359 with
                            | FStar_Syntax_Syntax.Tm_app uu____3363 -> false
                            | uu____3373 -> true in
                          if uu____3358
                          then e01
                          else
                            (let uu____3375 =
                               FStar_Syntax_Util.head_and_args e01 in
                             match uu____3375 with
                             | (head2,args) ->
                                 let uu____3401 =
                                   let uu____3402 =
                                     let uu____3403 =
                                       FStar_Syntax_Subst.compress head2 in
                                     uu____3403.FStar_Syntax_Syntax.n in
                                   match uu____3402 with
                                   | FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_reify ) -> true
                                   | uu____3406 -> false in
                                 if uu____3401
                                 then
                                   (match args with
                                    | x::[] -> Prims.fst x
                                    | uu____3422 ->
                                        failwith
                                          "Impossible : Reify applied to multiple arguments after normalization.")
                                 else e01) in
                        let e =
                          match args_e with
                          | uu____3430::[] -> e02
                          | uu____3443 ->
                              let uu____3449 =
                                let uu____3452 =
                                  let uu____3453 =
                                    let uu____3463 = FStar_List.tl args_e in
                                    (e02, uu____3463) in
                                  FStar_Syntax_Syntax.Tm_app uu____3453 in
                                FStar_Syntax_Syntax.mk uu____3452 in
                              uu____3449 None t0.FStar_Syntax_Syntax.pos in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3486),(arg,uu____3488)::[]) -> encode_term arg env
                 | uu____3506 ->
                     let uu____3514 = encode_args args_e env in
                     (match uu____3514 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3547 = encode_term head1 env in
                            match uu____3547 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3586 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3586 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3628  ->
                                                 fun uu____3629  ->
                                                   match (uu____3628,
                                                           uu____3629)
                                                   with
                                                   | ((bv,uu____3643),
                                                      (a,uu____3645)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3659 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3659
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3664 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3664 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3674 =
                                                   let uu____3678 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3683 =
                                                     let uu____3684 =
                                                       let uu____3685 =
                                                         let uu____3686 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3686 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3685 in
                                                     varops.mk_unique
                                                       uu____3684 in
                                                   (uu____3678,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3683) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3674 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3703 = lookup_free_var_sym env fv in
                            match uu____3703 with
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
                                let uu____3741 =
                                  let uu____3742 =
                                    let uu____3745 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3745 Prims.fst in
                                  FStar_All.pipe_right uu____3742 Prims.snd in
                                Some uu____3741
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3764,(FStar_Util.Inl t1,uu____3766),uu____3767)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3805,(FStar_Util.Inr c,uu____3807),uu____3808)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3846 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3866 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3866 in
                               let uu____3867 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3867 with
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
                                     | uu____3892 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3937 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3937 with
            | (bs1,body1,opening) ->
                let fallback uu____3952 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3957 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3957, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3968 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3968
                  | FStar_Util.Inr (eff,uu____3970) ->
                      let uu____3976 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3976 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body = reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4021 =
                            let uu____4022 =
                              FStar_Syntax_Syntax.get_lazy_comp lc in
                            uu____4022 () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___145_4025 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___145_4025.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___145_4025.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___145_4025.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___145_4025.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___145_4025.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___145_4025.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___145_4025.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___145_4025.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___145_4025.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___145_4025.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___145_4025.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___145_4025.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___145_4025.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___145_4025.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___145_4025.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___145_4025.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___145_4025.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___145_4025.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___145_4025.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___145_4025.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___145_4025.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___145_4025.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___145_4025.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4021 FStar_Syntax_Syntax.U_unknown in
                        let uu____4026 =
                          let uu____4027 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4027 in
                        FStar_Util.Inl uu____4026
                    | FStar_Util.Inr (eff_name,uu____4034) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4065 =
                        let uu____4066 =
                          let uu____4067 =
                            FStar_Syntax_Syntax.get_lazy_comp lc1 in
                          uu____4067 () in
                        FStar_Syntax_Subst.subst_comp opening uu____4066 in
                      FStar_All.pipe_right uu____4065
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4081 =
                        let uu____4082 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4082 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4090 =
                          let uu____4091 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4091 in
                        FStar_All.pipe_right uu____4090
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4095 =
                             let uu____4096 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4096 in
                           FStar_All.pipe_right uu____4095
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4107 =
                         let uu____4108 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4108 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4107);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4123 =
                       (is_impure lc1) &&
                         (let uu____4124 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4124) in
                     if uu____4123
                     then fallback ()
                     else
                       (let uu____4128 = encode_binders None bs1 env in
                        match uu____4128 with
                        | (vars,guards,envbody,decls,uu____4143) ->
                            let uu____4150 =
                              let uu____4158 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4158
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4150 with
                             | (lc2,body2) ->
                                 let uu____4183 = encode_term body2 envbody in
                                 (match uu____4183 with
                                  | (body3,decls') ->
                                      let key_body =
                                        let uu____4191 =
                                          let uu____4197 =
                                            let uu____4198 =
                                              let uu____4201 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____4201, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____4198 in
                                          ([], vars, uu____4197) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4191 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____4212 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____4212 with
                                       | Some (t1,uu____4227,uu____4228) ->
                                           let uu____4238 =
                                             let uu____4239 =
                                               let uu____4243 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (t1, uu____4243) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4239 in
                                           (uu____4238, [])
                                       | None  ->
                                           let uu____4254 =
                                             is_eta env vars body3 in
                                           (match uu____4254 with
                                            | Some t1 -> (t1, [])
                                            | None  ->
                                                let cvar_sorts =
                                                  FStar_List.map Prims.snd
                                                    cvars in
                                                let fsym =
                                                  let uu____4265 =
                                                    let uu____4266 =
                                                      FStar_Util.digest_of_string
                                                        tkey_hash in
                                                    Prims.strcat "Tm_abs_"
                                                      uu____4266 in
                                                  varops.mk_unique uu____4265 in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      None) in
                                                let f =
                                                  let uu____4271 =
                                                    let uu____4275 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars in
                                                    (fsym, uu____4275) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4271 in
                                                let app = mk_Apply f vars in
                                                let typing_f =
                                                  let uu____4283 =
                                                    codomain_eff lc2 in
                                                  match uu____4283 with
                                                  | None  -> []
                                                  | Some c ->
                                                      let tfun =
                                                        FStar_Syntax_Util.arrow
                                                          bs1 c in
                                                      let uu____4290 =
                                                        encode_term_pred None
                                                          tfun env f in
                                                      (match uu____4290 with
                                                       | (f_has_t,decls'') ->
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym in
                                                           let uu____4297 =
                                                             let uu____4299 =
                                                               let uu____4300
                                                                 =
                                                                 let uu____4304
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkForall
                                                                    ([[f]],
                                                                    cvars,
                                                                    f_has_t) in
                                                                 (uu____4304,
                                                                   (Some
                                                                    a_name),
                                                                   a_name) in
                                                               FStar_SMTEncoding_Term.Assume
                                                                 uu____4300 in
                                                             [uu____4299] in
                                                           FStar_List.append
                                                             decls''
                                                             uu____4297) in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____4312 =
                                                    let uu____4316 =
                                                      let uu____4317 =
                                                        let uu____4323 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars),
                                                          uu____4323) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____4317 in
                                                    (uu____4316,
                                                      (Some a_name), a_name) in
                                                  FStar_SMTEncoding_Term.Assume
                                                    uu____4312 in
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
           ((uu____4341,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4342;
                          FStar_Syntax_Syntax.lbunivs = uu____4343;
                          FStar_Syntax_Syntax.lbtyp = uu____4344;
                          FStar_Syntax_Syntax.lbeff = uu____4345;
                          FStar_Syntax_Syntax.lbdef = uu____4346;_}::uu____4347),uu____4348)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4366;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4368;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4384 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4397 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4397, [decl_e])))
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
              let uu____4439 = encode_term e1 env in
              match uu____4439 with
              | (ee1,decls1) ->
                  let uu____4446 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4446 with
                   | (xs,e21) ->
                       let uu____4460 = FStar_List.hd xs in
                       (match uu____4460 with
                        | (x1,uu____4468) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4470 = encode_body e21 env' in
                            (match uu____4470 with
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
            let uu____4492 =
              let uu____4496 =
                let uu____4497 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4497 in
              gen_term_var env uu____4496 in
            match uu____4492 with
            | (scrsym,scr',env1) ->
                let uu____4511 = encode_term e env1 in
                (match uu____4511 with
                 | (scr,decls) ->
                     let uu____4518 =
                       let encode_branch b uu____4534 =
                         match uu____4534 with
                         | (else_case,decls1) ->
                             let uu____4545 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4545 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4575  ->
                                       fun uu____4576  ->
                                         match (uu____4575, uu____4576) with
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
                                                       fun uu____4613  ->
                                                         match uu____4613
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4618 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4633 =
                                                     encode_term w1 env2 in
                                                   (match uu____4633 with
                                                    | (w2,decls21) ->
                                                        let uu____4641 =
                                                          let uu____4642 =
                                                            let uu____4645 =
                                                              let uu____4646
                                                                =
                                                                let uu____4649
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4649) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4646 in
                                                            (guard,
                                                              uu____4645) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4642 in
                                                        (uu____4641, decls21)) in
                                             (match uu____4618 with
                                              | (guard1,decls21) ->
                                                  let uu____4657 =
                                                    encode_br br env2 in
                                                  (match uu____4657 with
                                                   | (br1,decls3) ->
                                                       let uu____4665 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4665,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4518 with
                      | (match_tm,decls1) ->
                          let uu____4677 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4677, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4708 -> let uu____4709 = encode_one_pat env pat in [uu____4709]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4721 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4721
       then
         let uu____4722 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4722
       else ());
      (let uu____4724 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4724 with
       | (vars,pat_term) ->
           let uu____4734 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4757  ->
                     fun v1  ->
                       match uu____4757 with
                       | (env1,vars1) ->
                           let uu____4785 = gen_term_var env1 v1 in
                           (match uu____4785 with
                            | (xx,uu____4797,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4734 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4844 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4852 =
                        let uu____4855 = encode_const c in
                        (scrutinee, uu____4855) in
                      FStar_SMTEncoding_Util.mkEq uu____4852
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4874 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4874 with
                        | (uu____4878,uu____4879::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4881 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4902  ->
                                  match uu____4902 with
                                  | (arg,uu____4908) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4918 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4918)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4937 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4952 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4967 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4989  ->
                                  match uu____4989 with
                                  | (arg,uu____4998) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5008 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5008)) in
                      FStar_All.pipe_right uu____4967 FStar_List.flatten in
                let pat_term1 uu____5024 = encode_term pat_term env1 in
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
      let uu____5031 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5046  ->
                fun uu____5047  ->
                  match (uu____5046, uu____5047) with
                  | ((tms,decls),(t,uu____5067)) ->
                      let uu____5078 = encode_term t env in
                      (match uu____5078 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5031 with | (l1,decls) -> ((FStar_List.rev l1), decls)
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
            let uu____5116 = FStar_Syntax_Util.list_elements e in
            match uu____5116 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 []) in
          let one_pat p =
            let uu____5134 =
              let uu____5144 = FStar_Syntax_Util.unmeta p in
              FStar_All.pipe_right uu____5144 FStar_Syntax_Util.head_and_args in
            match uu____5134 with
            | (head1,args) ->
                let uu____5175 =
                  let uu____5183 =
                    let uu____5184 = FStar_Syntax_Util.un_uinst head1 in
                    uu____5184.FStar_Syntax_Syntax.n in
                  (uu____5183, args) in
                (match uu____5175 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5198,uu____5199)::(e,uu____5201)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5232)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5253 -> failwith "Unexpected pattern term") in
          let lemma_pats p =
            let elts = list_elements1 p in
            let smt_pat_or t1 =
              let uu____5286 =
                let uu____5296 = FStar_Syntax_Util.unmeta t1 in
                FStar_All.pipe_right uu____5296
                  FStar_Syntax_Util.head_and_args in
              match uu____5286 with
              | (head1,args) ->
                  let uu____5325 =
                    let uu____5333 =
                      let uu____5334 = FStar_Syntax_Util.un_uinst head1 in
                      uu____5334.FStar_Syntax_Syntax.n in
                    (uu____5333, args) in
                  (match uu____5325 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5347)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5367 -> None) in
            match elts with
            | t1::[] ->
                let uu____5385 = smt_pat_or t1 in
                (match uu____5385 with
                 | Some e ->
                     let uu____5401 = list_elements1 e in
                     FStar_All.pipe_right uu____5401
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5418 = list_elements1 branch1 in
                             FStar_All.pipe_right uu____5418
                               (FStar_List.map one_pat)))
                 | uu____5432 ->
                     let uu____5436 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat) in
                     [uu____5436])
            | uu____5467 ->
                let uu____5469 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat) in
                [uu____5469] in
          let uu____5500 =
            let uu____5516 =
              let uu____5517 = FStar_Syntax_Subst.compress t in
              uu____5517.FStar_Syntax_Syntax.n in
            match uu____5516 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5547 = FStar_Syntax_Subst.open_comp binders c in
                (match uu____5547 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5582;
                            FStar_Syntax_Syntax.effect_name = uu____5583;
                            FStar_Syntax_Syntax.result_typ = uu____5584;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5586)::(post,uu____5588)::(pats,uu____5590)::[];
                            FStar_Syntax_Syntax.flags = uu____5591;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats in
                          let uu____5625 = lemma_pats pats' in
                          (binders1, pre, post, uu____5625)
                      | uu____5644 -> failwith "impos"))
            | uu____5660 -> failwith "Impos" in
          match uu____5500 with
          | (binders,pre,post,patterns) ->
              let uu____5704 = encode_binders None binders env in
              (match uu____5704 with
               | (vars,guards,env1,decls,uu____5719) ->
                   let uu____5726 =
                     let uu____5733 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5764 =
                                 let uu____5769 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5785  ->
                                           match uu____5785 with
                                           | (t1,uu____5792) ->
                                               encode_term t1
                                                 (let uu___146_5795 = env1 in
                                                  {
                                                    bindings =
                                                      (uu___146_5795.bindings);
                                                    depth =
                                                      (uu___146_5795.depth);
                                                    tcenv =
                                                      (uu___146_5795.tcenv);
                                                    warn =
                                                      (uu___146_5795.warn);
                                                    cache =
                                                      (uu___146_5795.cache);
                                                    nolabels =
                                                      (uu___146_5795.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___146_5795.encode_non_total_function_typ)
                                                  }))) in
                                 FStar_All.pipe_right uu____5769
                                   FStar_List.unzip in
                               match uu____5764 with
                               | (pats,decls1) -> (pats, decls1))) in
                     FStar_All.pipe_right uu____5733 FStar_List.unzip in
                   (match uu____5726 with
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
                                           let uu____5859 =
                                             let uu____5860 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5860 e in
                                           uu____5859 :: p))
                               | uu____5861 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5890 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e in
                                                 uu____5890 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5898 =
                                           let uu____5899 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort) in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5899 tl1 in
                                         aux uu____5898 vars2
                                     | uu____5900 -> pats in
                                   let uu____5904 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort) in
                                   aux uu____5904 vars) in
                        let env2 =
                          let uu___147_5906 = env1 in
                          {
                            bindings = (uu___147_5906.bindings);
                            depth = (uu___147_5906.depth);
                            tcenv = (uu___147_5906.tcenv);
                            warn = (uu___147_5906.warn);
                            cache = (uu___147_5906.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___147_5906.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___147_5906.encode_non_total_function_typ)
                          } in
                        let uu____5907 =
                          let uu____5910 = FStar_Syntax_Util.unmeta pre in
                          encode_formula uu____5910 env2 in
                        (match uu____5907 with
                         | (pre1,decls'') ->
                             let uu____5915 =
                               let uu____5918 = FStar_Syntax_Util.unmeta post in
                               encode_formula uu____5918 env2 in
                             (match uu____5915 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls''')) in
                                  let uu____5925 =
                                    let uu____5926 =
                                      let uu____5932 =
                                        let uu____5933 =
                                          let uu____5936 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards) in
                                          (uu____5936, post1) in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5933 in
                                      (pats1, vars, uu____5932) in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5926 in
                                  (uu____5925, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5949 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5949
        then
          let uu____5950 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5951 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5950 uu____5951
        else () in
      let enc f r l =
        let uu____5978 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5991 = encode_term (Prims.fst x) env in
                 match uu____5991 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5978 with
        | (decls,args) ->
            let uu____6008 =
              let uu___148_6009 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___148_6009.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___148_6009.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6008, decls) in
      let const_op f r uu____6028 = let uu____6031 = f r in (uu____6031, []) in
      let un_op f l =
        let uu____6047 = FStar_List.hd l in FStar_All.pipe_left f uu____6047 in
      let bin_op f uu___120_6060 =
        match uu___120_6060 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6068 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6095 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6104  ->
                 match uu____6104 with
                 | (t,uu____6112) ->
                     let uu____6113 = encode_formula t env in
                     (match uu____6113 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6095 with
        | (decls,phis) ->
            let uu____6130 =
              let uu___149_6131 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___149_6131.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___149_6131.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6130, decls) in
      let eq_op r uu___121_6147 =
        match uu___121_6147 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6207 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6207 r [e1; e2]
        | l ->
            let uu____6227 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6227 r l in
      let mk_imp1 r uu___122_6246 =
        match uu___122_6246 with
        | (lhs,uu____6250)::(rhs,uu____6252)::[] ->
            let uu____6273 = encode_formula rhs env in
            (match uu____6273 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6282) ->
                      (l1, decls1)
                  | uu____6285 ->
                      let uu____6286 = encode_formula lhs env in
                      (match uu____6286 with
                       | (l2,decls2) ->
                           let uu____6293 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6293, (FStar_List.append decls1 decls2)))))
        | uu____6295 -> failwith "impossible" in
      let mk_ite r uu___123_6310 =
        match uu___123_6310 with
        | (guard,uu____6314)::(_then,uu____6316)::(_else,uu____6318)::[] ->
            let uu____6347 = encode_formula guard env in
            (match uu____6347 with
             | (g,decls1) ->
                 let uu____6354 = encode_formula _then env in
                 (match uu____6354 with
                  | (t,decls2) ->
                      let uu____6361 = encode_formula _else env in
                      (match uu____6361 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6370 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6389 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6389 in
      let connectives =
        let uu____6401 =
          let uu____6410 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6410) in
        let uu____6423 =
          let uu____6433 =
            let uu____6442 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6442) in
          let uu____6455 =
            let uu____6465 =
              let uu____6475 =
                let uu____6484 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6484) in
              let uu____6497 =
                let uu____6507 =
                  let uu____6517 =
                    let uu____6526 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6526) in
                  [uu____6517;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6507 in
              uu____6475 :: uu____6497 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6465 in
          uu____6433 :: uu____6455 in
        uu____6401 :: uu____6423 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6688 = encode_formula phi' env in
            (match uu____6688 with
             | (phi2,decls) ->
                 let uu____6695 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6695, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6696 ->
            let uu____6701 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6701 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6730 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6730 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6738;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6740;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6756 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6756 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6788::(x,uu____6790)::(t,uu____6792)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6826 = encode_term x env in
                 (match uu____6826 with
                  | (x1,decls) ->
                      let uu____6833 = encode_term t env in
                      (match uu____6833 with
                       | (t1,decls') ->
                           let uu____6840 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6840, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6844)::(msg,uu____6846)::(phi2,uu____6848)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6882 =
                   let uu____6885 =
                     let uu____6886 = FStar_Syntax_Subst.compress r in
                     uu____6886.FStar_Syntax_Syntax.n in
                   let uu____6889 =
                     let uu____6890 = FStar_Syntax_Subst.compress msg in
                     uu____6890.FStar_Syntax_Syntax.n in
                   (uu____6885, uu____6889) in
                 (match uu____6882 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6897))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6913 -> fallback phi2)
             | uu____6916 when head_redex env head2 ->
                 let uu____6924 = whnf env phi1 in
                 encode_formula uu____6924 env
             | uu____6925 ->
                 let uu____6933 = encode_term phi1 env in
                 (match uu____6933 with
                  | (tt,decls) ->
                      let uu____6940 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___150_6941 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___150_6941.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___150_6941.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6940, decls)))
        | uu____6944 ->
            let uu____6945 = encode_term phi1 env in
            (match uu____6945 with
             | (tt,decls) ->
                 let uu____6952 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___151_6953 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___151_6953.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___151_6953.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6952, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6980 = encode_binders None bs env1 in
        match uu____6980 with
        | (vars,guards,env2,decls,uu____7002) ->
            let uu____7009 =
              let uu____7016 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7039 =
                          let uu____7044 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7058  ->
                                    match uu____7058 with
                                    | (t,uu____7064) ->
                                        encode_term t
                                          (let uu___152_7065 = env2 in
                                           {
                                             bindings =
                                               (uu___152_7065.bindings);
                                             depth = (uu___152_7065.depth);
                                             tcenv = (uu___152_7065.tcenv);
                                             warn = (uu___152_7065.warn);
                                             cache = (uu___152_7065.cache);
                                             nolabels =
                                               (uu___152_7065.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___152_7065.encode_non_total_function_typ)
                                           }))) in
                          FStar_All.pipe_right uu____7044 FStar_List.unzip in
                        match uu____7039 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7016 FStar_List.unzip in
            (match uu____7009 with
             | (pats,decls') ->
                 let uu____7117 = encode_formula body env2 in
                 (match uu____7117 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7136;
                             FStar_SMTEncoding_Term.rng = uu____7137;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7145 -> guards in
                      let uu____7148 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7148, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7182  ->
                   match uu____7182 with
                   | (x,uu____7186) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7192 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7198 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7198) uu____7192 tl1 in
             let uu____7200 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7212  ->
                       match uu____7212 with
                       | (b,uu____7216) ->
                           let uu____7217 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7217)) in
             (match uu____7200 with
              | None  -> ()
              | Some (x,uu____7221) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7231 =
                    let uu____7232 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7232 in
                  FStar_Errors.warn pos uu____7231) in
       let uu____7233 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7233 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7239 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7275  ->
                     match uu____7275 with
                     | (l,uu____7285) -> FStar_Ident.lid_equals op l)) in
           (match uu____7239 with
            | None  -> fallback phi1
            | Some (uu____7308,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7337 = encode_q_body env vars pats body in
             match uu____7337 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7363 =
                     let uu____7369 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7369) in
                   FStar_SMTEncoding_Term.mkForall uu____7363
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7381 = encode_q_body env vars pats body in
             match uu____7381 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7406 =
                   let uu____7407 =
                     let uu____7413 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7413) in
                   FStar_SMTEncoding_Term.mkExists uu____7407
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7406, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7462 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7462 with
  | (asym,a) ->
      let uu____7467 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7467 with
       | (xsym,x) ->
           let uu____7472 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7472 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7502 =
                      let uu____7508 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7508, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7502 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7523 =
                      let uu____7527 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7527) in
                    FStar_SMTEncoding_Util.mkApp uu____7523 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7535 =
                    let uu____7537 =
                      let uu____7539 =
                        let uu____7541 =
                          let uu____7542 =
                            let uu____7546 =
                              let uu____7547 =
                                let uu____7553 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7553) in
                              FStar_SMTEncoding_Util.mkForall uu____7547 in
                            (uu____7546, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Term.Assume uu____7542 in
                        let uu____7562 =
                          let uu____7564 =
                            let uu____7565 =
                              let uu____7569 =
                                let uu____7570 =
                                  let uu____7576 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7576) in
                                FStar_SMTEncoding_Util.mkForall uu____7570 in
                              (uu____7569,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Term.Assume uu____7565 in
                          [uu____7564] in
                        uu____7541 :: uu____7562 in
                      xtok_decl :: uu____7539 in
                    xname_decl :: uu____7537 in
                  (xtok1, uu____7535) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7625 =
                    let uu____7633 =
                      let uu____7639 =
                        let uu____7640 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7640 in
                      quant axy uu____7639 in
                    (FStar_Syntax_Const.op_Eq, uu____7633) in
                  let uu____7646 =
                    let uu____7655 =
                      let uu____7663 =
                        let uu____7669 =
                          let uu____7670 =
                            let uu____7671 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7671 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7670 in
                        quant axy uu____7669 in
                      (FStar_Syntax_Const.op_notEq, uu____7663) in
                    let uu____7677 =
                      let uu____7686 =
                        let uu____7694 =
                          let uu____7700 =
                            let uu____7701 =
                              let uu____7702 =
                                let uu____7705 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7706 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7705, uu____7706) in
                              FStar_SMTEncoding_Util.mkLT uu____7702 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7701 in
                          quant xy uu____7700 in
                        (FStar_Syntax_Const.op_LT, uu____7694) in
                      let uu____7712 =
                        let uu____7721 =
                          let uu____7729 =
                            let uu____7735 =
                              let uu____7736 =
                                let uu____7737 =
                                  let uu____7740 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7741 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7740, uu____7741) in
                                FStar_SMTEncoding_Util.mkLTE uu____7737 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7736 in
                            quant xy uu____7735 in
                          (FStar_Syntax_Const.op_LTE, uu____7729) in
                        let uu____7747 =
                          let uu____7756 =
                            let uu____7764 =
                              let uu____7770 =
                                let uu____7771 =
                                  let uu____7772 =
                                    let uu____7775 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7776 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7775, uu____7776) in
                                  FStar_SMTEncoding_Util.mkGT uu____7772 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7771 in
                              quant xy uu____7770 in
                            (FStar_Syntax_Const.op_GT, uu____7764) in
                          let uu____7782 =
                            let uu____7791 =
                              let uu____7799 =
                                let uu____7805 =
                                  let uu____7806 =
                                    let uu____7807 =
                                      let uu____7810 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7811 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7810, uu____7811) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7807 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7806 in
                                quant xy uu____7805 in
                              (FStar_Syntax_Const.op_GTE, uu____7799) in
                            let uu____7817 =
                              let uu____7826 =
                                let uu____7834 =
                                  let uu____7840 =
                                    let uu____7841 =
                                      let uu____7842 =
                                        let uu____7845 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7846 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7845, uu____7846) in
                                      FStar_SMTEncoding_Util.mkSub uu____7842 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7841 in
                                  quant xy uu____7840 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7834) in
                              let uu____7852 =
                                let uu____7861 =
                                  let uu____7869 =
                                    let uu____7875 =
                                      let uu____7876 =
                                        let uu____7877 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7877 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7876 in
                                    quant qx uu____7875 in
                                  (FStar_Syntax_Const.op_Minus, uu____7869) in
                                let uu____7883 =
                                  let uu____7892 =
                                    let uu____7900 =
                                      let uu____7906 =
                                        let uu____7907 =
                                          let uu____7908 =
                                            let uu____7911 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7912 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7911, uu____7912) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7908 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7907 in
                                      quant xy uu____7906 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7900) in
                                  let uu____7918 =
                                    let uu____7927 =
                                      let uu____7935 =
                                        let uu____7941 =
                                          let uu____7942 =
                                            let uu____7943 =
                                              let uu____7946 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7947 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7946, uu____7947) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7943 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7942 in
                                        quant xy uu____7941 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7935) in
                                    let uu____7953 =
                                      let uu____7962 =
                                        let uu____7970 =
                                          let uu____7976 =
                                            let uu____7977 =
                                              let uu____7978 =
                                                let uu____7981 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7982 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7981, uu____7982) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7978 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7977 in
                                          quant xy uu____7976 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7970) in
                                      let uu____7988 =
                                        let uu____7997 =
                                          let uu____8005 =
                                            let uu____8011 =
                                              let uu____8012 =
                                                let uu____8013 =
                                                  let uu____8016 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8017 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8016, uu____8017) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8013 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8012 in
                                            quant xy uu____8011 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8005) in
                                        let uu____8023 =
                                          let uu____8032 =
                                            let uu____8040 =
                                              let uu____8046 =
                                                let uu____8047 =
                                                  let uu____8048 =
                                                    let uu____8051 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8052 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8051, uu____8052) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8048 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8047 in
                                              quant xy uu____8046 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8040) in
                                          let uu____8058 =
                                            let uu____8067 =
                                              let uu____8075 =
                                                let uu____8081 =
                                                  let uu____8082 =
                                                    let uu____8083 =
                                                      let uu____8086 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8087 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8086,
                                                        uu____8087) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8083 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8082 in
                                                quant xy uu____8081 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8075) in
                                            let uu____8093 =
                                              let uu____8102 =
                                                let uu____8110 =
                                                  let uu____8116 =
                                                    let uu____8117 =
                                                      let uu____8118 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8118 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8117 in
                                                  quant qx uu____8116 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8110) in
                                              [uu____8102] in
                                            uu____8067 :: uu____8093 in
                                          uu____8032 :: uu____8058 in
                                        uu____7997 :: uu____8023 in
                                      uu____7962 :: uu____7988 in
                                    uu____7927 :: uu____7953 in
                                  uu____7892 :: uu____7918 in
                                uu____7861 :: uu____7883 in
                              uu____7826 :: uu____7852 in
                            uu____7791 :: uu____7817 in
                          uu____7756 :: uu____7782 in
                        uu____7721 :: uu____7747 in
                      uu____7686 :: uu____7712 in
                    uu____7655 :: uu____7677 in
                  uu____7625 :: uu____7646 in
                let mk1 l v1 =
                  let uu____8246 =
                    let uu____8251 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8283  ->
                              match uu____8283 with
                              | (l',uu____8292) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8251
                      (FStar_Option.map
                         (fun uu____8325  ->
                            match uu____8325 with | (uu____8336,b) -> b v1)) in
                  FStar_All.pipe_right uu____8246 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8377  ->
                          match uu____8377 with
                          | (l',uu____8386) -> FStar_Ident.lid_equals l l')) in
                { mk = mk1; is }))
let pretype_axiom:
  FStar_SMTEncoding_Term.term ->
    (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.decl
  =
  fun tapp  ->
    fun vars  ->
      let uu____8409 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      match uu____8409 with
      | (xxsym,xx) ->
          let uu____8414 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
          (match uu____8414 with
           | (ffsym,ff) ->
               let xx_has_type =
                 FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
               let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
               let uu____8421 =
                 let uu____8425 =
                   let uu____8426 =
                     let uu____8432 =
                       let uu____8433 =
                         let uu____8436 =
                           let uu____8437 =
                             let uu____8440 =
                               FStar_SMTEncoding_Util.mkApp ("PreType", [xx]) in
                             (tapp, uu____8440) in
                           FStar_SMTEncoding_Util.mkEq uu____8437 in
                         (xx_has_type, uu____8436) in
                       FStar_SMTEncoding_Util.mkImp uu____8433 in
                     ([[xx_has_type]],
                       ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                       (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                       uu____8432) in
                   FStar_SMTEncoding_Util.mkForall uu____8426 in
                 let uu____8453 =
                   let uu____8454 =
                     let uu____8455 = FStar_Util.digest_of_string tapp_hash in
                     Prims.strcat "pretyping_" uu____8455 in
                   varops.mk_unique uu____8454 in
                 (uu____8425, (Some "pretyping"), uu____8453) in
               FStar_SMTEncoding_Term.Assume uu____8421)
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
    let uu____8485 =
      let uu____8486 =
        let uu____8490 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8490, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Term.Assume uu____8486 in
    let uu____8492 =
      let uu____8494 =
        let uu____8495 =
          let uu____8499 =
            let uu____8500 =
              let uu____8506 =
                let uu____8507 =
                  let uu____8510 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8510) in
                FStar_SMTEncoding_Util.mkImp uu____8507 in
              ([[typing_pred]], [xx], uu____8506) in
            mkForall_fuel uu____8500 in
          (uu____8499, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8495 in
      [uu____8494] in
    uu____8485 :: uu____8492 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8538 =
      let uu____8539 =
        let uu____8543 =
          let uu____8544 =
            let uu____8550 =
              let uu____8553 =
                let uu____8555 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8555] in
              [uu____8553] in
            let uu____8558 =
              let uu____8559 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8559 tt in
            (uu____8550, [bb], uu____8558) in
          FStar_SMTEncoding_Util.mkForall uu____8544 in
        (uu____8543, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Term.Assume uu____8539 in
    let uu____8570 =
      let uu____8572 =
        let uu____8573 =
          let uu____8577 =
            let uu____8578 =
              let uu____8584 =
                let uu____8585 =
                  let uu____8588 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8588) in
                FStar_SMTEncoding_Util.mkImp uu____8585 in
              ([[typing_pred]], [xx], uu____8584) in
            mkForall_fuel uu____8578 in
          (uu____8577, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8573 in
      [uu____8572] in
    uu____8538 :: uu____8570 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8622 =
        let uu____8623 =
          let uu____8627 =
            let uu____8629 =
              let uu____8631 =
                let uu____8633 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8634 =
                  let uu____8636 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8636] in
                uu____8633 :: uu____8634 in
              tt :: uu____8631 in
            tt :: uu____8629 in
          ("Prims.Precedes", uu____8627) in
        FStar_SMTEncoding_Util.mkApp uu____8623 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8622 in
    let precedes_y_x =
      let uu____8639 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8639 in
    let uu____8641 =
      let uu____8642 =
        let uu____8646 =
          let uu____8647 =
            let uu____8653 =
              let uu____8656 =
                let uu____8658 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8658] in
              [uu____8656] in
            let uu____8661 =
              let uu____8662 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8662 tt in
            (uu____8653, [bb], uu____8661) in
          FStar_SMTEncoding_Util.mkForall uu____8647 in
        (uu____8646, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Term.Assume uu____8642 in
    let uu____8673 =
      let uu____8675 =
        let uu____8676 =
          let uu____8680 =
            let uu____8681 =
              let uu____8687 =
                let uu____8688 =
                  let uu____8691 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8691) in
                FStar_SMTEncoding_Util.mkImp uu____8688 in
              ([[typing_pred]], [xx], uu____8687) in
            mkForall_fuel uu____8681 in
          (uu____8680, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8676 in
      let uu____8704 =
        let uu____8706 =
          let uu____8707 =
            let uu____8711 =
              let uu____8712 =
                let uu____8718 =
                  let uu____8719 =
                    let uu____8722 =
                      let uu____8723 =
                        let uu____8725 =
                          let uu____8727 =
                            let uu____8729 =
                              let uu____8730 =
                                let uu____8733 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8734 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8733, uu____8734) in
                              FStar_SMTEncoding_Util.mkGT uu____8730 in
                            let uu____8735 =
                              let uu____8737 =
                                let uu____8738 =
                                  let uu____8741 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8742 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8741, uu____8742) in
                                FStar_SMTEncoding_Util.mkGTE uu____8738 in
                              let uu____8743 =
                                let uu____8745 =
                                  let uu____8746 =
                                    let uu____8749 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8750 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8749, uu____8750) in
                                  FStar_SMTEncoding_Util.mkLT uu____8746 in
                                [uu____8745] in
                              uu____8737 :: uu____8743 in
                            uu____8729 :: uu____8735 in
                          typing_pred_y :: uu____8727 in
                        typing_pred :: uu____8725 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8723 in
                    (uu____8722, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8719 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8718) in
              mkForall_fuel uu____8712 in
            (uu____8711, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Term.Assume uu____8707 in
        [uu____8706] in
      uu____8675 :: uu____8704 in
    uu____8641 :: uu____8673 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8780 =
      let uu____8781 =
        let uu____8785 =
          let uu____8786 =
            let uu____8792 =
              let uu____8795 =
                let uu____8797 = FStar_SMTEncoding_Term.boxString b in
                [uu____8797] in
              [uu____8795] in
            let uu____8800 =
              let uu____8801 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8801 tt in
            (uu____8792, [bb], uu____8800) in
          FStar_SMTEncoding_Util.mkForall uu____8786 in
        (uu____8785, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Term.Assume uu____8781 in
    let uu____8812 =
      let uu____8814 =
        let uu____8815 =
          let uu____8819 =
            let uu____8820 =
              let uu____8826 =
                let uu____8827 =
                  let uu____8830 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8830) in
                FStar_SMTEncoding_Util.mkImp uu____8827 in
              ([[typing_pred]], [xx], uu____8826) in
            mkForall_fuel uu____8820 in
          (uu____8819, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8815 in
      [uu____8814] in
    uu____8780 :: uu____8812 in
  let mk_ref1 env reft_name uu____8852 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8863 =
        let uu____8867 =
          let uu____8869 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8869] in
        (reft_name, uu____8867) in
      FStar_SMTEncoding_Util.mkApp uu____8863 in
    let refb =
      let uu____8872 =
        let uu____8876 =
          let uu____8878 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8878] in
        (reft_name, uu____8876) in
      FStar_SMTEncoding_Util.mkApp uu____8872 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8882 =
      let uu____8883 =
        let uu____8887 =
          let uu____8888 =
            let uu____8894 =
              let uu____8895 =
                let uu____8898 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8898) in
              FStar_SMTEncoding_Util.mkImp uu____8895 in
            ([[typing_pred]], [xx; aa], uu____8894) in
          mkForall_fuel uu____8888 in
        (uu____8887, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Term.Assume uu____8883 in
    let uu____8913 =
      let uu____8915 =
        let uu____8916 =
          let uu____8920 =
            let uu____8921 =
              let uu____8927 =
                let uu____8928 =
                  let uu____8931 =
                    FStar_SMTEncoding_Util.mkAnd (typing_pred, typing_pred_b) in
                  let uu____8932 =
                    let uu____8933 =
                      let uu____8936 = FStar_SMTEncoding_Util.mkFreeV aa in
                      let uu____8937 = FStar_SMTEncoding_Util.mkFreeV bb in
                      (uu____8936, uu____8937) in
                    FStar_SMTEncoding_Util.mkEq uu____8933 in
                  (uu____8931, uu____8932) in
                FStar_SMTEncoding_Util.mkImp uu____8928 in
              ([[typing_pred; typing_pred_b]], [xx; aa; bb], uu____8927) in
            mkForall_fuel' (Prims.parse_int "2") uu____8921 in
          (uu____8920, (Some "ref typing is injective"), "ref_injectivity") in
        FStar_SMTEncoding_Term.Assume uu____8916 in
      [uu____8915] in
    uu____8882 :: uu____8913 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8979 =
      let uu____8980 =
        let uu____8984 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8984, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Term.Assume uu____8980 in
    [uu____8979] in
  let mk_and_interp env conj uu____8995 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9005 =
        let uu____9009 =
          let uu____9011 = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
          [uu____9011] in
        ("Valid", uu____9009) in
      FStar_SMTEncoding_Util.mkApp uu____9005 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9018 =
      let uu____9019 =
        let uu____9023 =
          let uu____9024 =
            let uu____9030 =
              let uu____9031 =
                let uu____9034 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9034, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9031 in
            ([[valid]], [aa; bb], uu____9030) in
          FStar_SMTEncoding_Util.mkForall uu____9024 in
        (uu____9023, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Term.Assume uu____9019 in
    [uu____9018] in
  let mk_or_interp env disj uu____9058 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9068 =
        let uu____9072 =
          let uu____9074 = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
          [uu____9074] in
        ("Valid", uu____9072) in
      FStar_SMTEncoding_Util.mkApp uu____9068 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9081 =
      let uu____9082 =
        let uu____9086 =
          let uu____9087 =
            let uu____9093 =
              let uu____9094 =
                let uu____9097 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9097, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9094 in
            ([[valid]], [aa; bb], uu____9093) in
          FStar_SMTEncoding_Util.mkForall uu____9087 in
        (uu____9086, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Term.Assume uu____9082 in
    [uu____9081] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let valid =
      let uu____9135 =
        let uu____9139 =
          let uu____9141 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
          [uu____9141] in
        ("Valid", uu____9139) in
      FStar_SMTEncoding_Util.mkApp uu____9135 in
    let uu____9144 =
      let uu____9145 =
        let uu____9149 =
          let uu____9150 =
            let uu____9156 =
              let uu____9157 =
                let uu____9160 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9160, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9157 in
            ([[valid]], [aa; xx1; yy1], uu____9156) in
          FStar_SMTEncoding_Util.mkForall uu____9150 in
        (uu____9149, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Term.Assume uu____9145 in
    [uu____9144] in
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
      let uu____9204 =
        let uu____9208 =
          let uu____9210 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
          [uu____9210] in
        ("Valid", uu____9208) in
      FStar_SMTEncoding_Util.mkApp uu____9204 in
    let uu____9213 =
      let uu____9214 =
        let uu____9218 =
          let uu____9219 =
            let uu____9225 =
              let uu____9226 =
                let uu____9229 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9229, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9226 in
            ([[valid]], [aa; bb; xx1; yy1], uu____9225) in
          FStar_SMTEncoding_Util.mkForall uu____9219 in
        (uu____9218, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Term.Assume uu____9214 in
    [uu____9213] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9267 =
        let uu____9271 =
          let uu____9273 = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
          [uu____9273] in
        ("Valid", uu____9271) in
      FStar_SMTEncoding_Util.mkApp uu____9267 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9280 =
      let uu____9281 =
        let uu____9285 =
          let uu____9286 =
            let uu____9292 =
              let uu____9293 =
                let uu____9296 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9296, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9293 in
            ([[valid]], [aa; bb], uu____9292) in
          FStar_SMTEncoding_Util.mkForall uu____9286 in
        (uu____9285, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Term.Assume uu____9281 in
    [uu____9280] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9330 =
        let uu____9334 =
          let uu____9336 = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
          [uu____9336] in
        ("Valid", uu____9334) in
      FStar_SMTEncoding_Util.mkApp uu____9330 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9343 =
      let uu____9344 =
        let uu____9348 =
          let uu____9349 =
            let uu____9355 =
              let uu____9356 =
                let uu____9359 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9359, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9356 in
            ([[valid]], [aa; bb], uu____9355) in
          FStar_SMTEncoding_Util.mkForall uu____9349 in
        (uu____9348, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Term.Assume uu____9344 in
    [uu____9343] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let valid =
      let uu____9389 =
        let uu____9393 =
          let uu____9395 = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
          [uu____9395] in
        ("Valid", uu____9393) in
      FStar_SMTEncoding_Util.mkApp uu____9389 in
    let not_valid_a =
      let uu____9399 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9399 in
    let uu____9401 =
      let uu____9402 =
        let uu____9406 =
          let uu____9407 =
            let uu____9413 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[valid]], [aa], uu____9413) in
          FStar_SMTEncoding_Util.mkForall uu____9407 in
        (uu____9406, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Term.Assume uu____9402 in
    [uu____9401] in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let valid =
      let uu____9449 =
        let uu____9453 =
          let uu____9455 = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b]) in
          [uu____9455] in
        ("Valid", uu____9453) in
      FStar_SMTEncoding_Util.mkApp uu____9449 in
    let valid_b_x =
      let uu____9459 =
        let uu____9463 =
          let uu____9465 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9465] in
        ("Valid", uu____9463) in
      FStar_SMTEncoding_Util.mkApp uu____9459 in
    let uu____9467 =
      let uu____9468 =
        let uu____9472 =
          let uu____9473 =
            let uu____9479 =
              let uu____9480 =
                let uu____9483 =
                  let uu____9484 =
                    let uu____9490 =
                      let uu____9493 =
                        let uu____9495 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9495] in
                      [uu____9493] in
                    let uu____9498 =
                      let uu____9499 =
                        let uu____9502 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9502, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9499 in
                    (uu____9490, [xx1], uu____9498) in
                  FStar_SMTEncoding_Util.mkForall uu____9484 in
                (uu____9483, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9480 in
            ([[valid]], [aa; bb], uu____9479) in
          FStar_SMTEncoding_Util.mkForall uu____9473 in
        (uu____9472, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Term.Assume uu____9468 in
    [uu____9467] in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let valid =
      let uu____9549 =
        let uu____9553 =
          let uu____9555 = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b]) in
          [uu____9555] in
        ("Valid", uu____9553) in
      FStar_SMTEncoding_Util.mkApp uu____9549 in
    let valid_b_x =
      let uu____9559 =
        let uu____9563 =
          let uu____9565 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9565] in
        ("Valid", uu____9563) in
      FStar_SMTEncoding_Util.mkApp uu____9559 in
    let uu____9567 =
      let uu____9568 =
        let uu____9572 =
          let uu____9573 =
            let uu____9579 =
              let uu____9580 =
                let uu____9583 =
                  let uu____9584 =
                    let uu____9590 =
                      let uu____9593 =
                        let uu____9595 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9595] in
                      [uu____9593] in
                    let uu____9598 =
                      let uu____9599 =
                        let uu____9602 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9602, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9599 in
                    (uu____9590, [xx1], uu____9598) in
                  FStar_SMTEncoding_Util.mkExists uu____9584 in
                (uu____9583, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9580 in
            ([[valid]], [aa; bb], uu____9579) in
          FStar_SMTEncoding_Util.mkForall uu____9573 in
        (uu____9572, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Term.Assume uu____9568 in
    [uu____9567] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9638 =
      let uu____9639 =
        let uu____9643 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9644 = varops.mk_unique "typing_range_const" in
        (uu____9643, (Some "Range_const typing"), uu____9644) in
      FStar_SMTEncoding_Term.Assume uu____9639 in
    [uu____9638] in
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
          let uu____9906 =
            FStar_Util.find_opt
              (fun uu____9924  ->
                 match uu____9924 with
                 | (l,uu____9934) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9906 with
          | None  -> []
          | Some (uu____9956,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9993 = encode_function_type_as_formula None None t env in
        match uu____9993 with
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
            let uu____10025 =
              (let uu____10026 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10026) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10025
            then
              let uu____10030 = new_term_constant_and_tok_from_lid env lid in
              match uu____10030 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10042 =
                      let uu____10043 = FStar_Syntax_Subst.compress t_norm in
                      uu____10043.FStar_Syntax_Syntax.n in
                    match uu____10042 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10048) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10065  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10068 -> [] in
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
              (let uu____10077 = prims.is lid in
               if uu____10077
               then
                 let vname = varops.new_fvar lid in
                 let uu____10082 = prims.mk lid vname in
                 match uu____10082 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10097 =
                    let uu____10103 = curried_arrow_formals_comp t_norm in
                    match uu____10103 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10114 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10114
                          then
                            let uu____10115 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___153_10116 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___153_10116.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___153_10116.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___153_10116.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___153_10116.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___153_10116.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___153_10116.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___153_10116.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___153_10116.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___153_10116.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___153_10116.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___153_10116.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___153_10116.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___153_10116.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___153_10116.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___153_10116.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___153_10116.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___153_10116.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___153_10116.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___153_10116.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___153_10116.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___153_10116.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___153_10116.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___153_10116.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10115
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10123 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10123)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10097 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10150 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10150 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10163 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___124_10187  ->
                                     match uu___124_10187 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10190 =
                                           FStar_Util.prefix vars in
                                         (match uu____10190 with
                                          | (uu____10201,(xxsym,uu____10203))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10213 =
                                                let uu____10214 =
                                                  let uu____10218 =
                                                    let uu____10219 =
                                                      let uu____10225 =
                                                        let uu____10226 =
                                                          let uu____10229 =
                                                            let uu____10230 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10230 in
                                                          (vapp, uu____10229) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10226 in
                                                      ([[vapp]], vars,
                                                        uu____10225) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10219 in
                                                  (uu____10218,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10214 in
                                              [uu____10213])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10241 =
                                           FStar_Util.prefix vars in
                                         (match uu____10241 with
                                          | (uu____10252,(xxsym,uu____10254))
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
                                              let uu____10268 =
                                                let uu____10269 =
                                                  let uu____10273 =
                                                    let uu____10274 =
                                                      let uu____10280 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10280) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10274 in
                                                  (uu____10273,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10269 in
                                              [uu____10268])
                                     | uu____10289 -> [])) in
                           let uu____10290 = encode_binders None formals env1 in
                           (match uu____10290 with
                            | (vars,guards,env',decls1,uu____10306) ->
                                let uu____10313 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10318 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10318, decls1)
                                  | Some p ->
                                      let uu____10320 = encode_formula p env' in
                                      (match uu____10320 with
                                       | (g,ds) ->
                                           let uu____10327 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10327,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10313 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10336 =
                                         let uu____10340 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10340) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10336 in
                                     let uu____10345 =
                                       let vname_decl =
                                         let uu____10350 =
                                           let uu____10356 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10361  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10356,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10350 in
                                       let uu____10366 =
                                         let env2 =
                                           let uu___154_10370 = env1 in
                                           {
                                             bindings =
                                               (uu___154_10370.bindings);
                                             depth = (uu___154_10370.depth);
                                             tcenv = (uu___154_10370.tcenv);
                                             warn = (uu___154_10370.warn);
                                             cache = (uu___154_10370.cache);
                                             nolabels =
                                               (uu___154_10370.nolabels);
                                             use_zfuel_name =
                                               (uu___154_10370.use_zfuel_name);
                                             encode_non_total_function_typ
                                           } in
                                         let uu____10371 =
                                           let uu____10372 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10372 in
                                         if uu____10371
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10366 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             FStar_SMTEncoding_Term.Assume
                                               (tok_typing,
                                                 (Some
                                                    "function token typing"),
                                                 (Prims.strcat
                                                    "function_token_typing_"
                                                    vname)) in
                                           let uu____10383 =
                                             match formals with
                                             | [] ->
                                                 let uu____10392 =
                                                   let uu____10393 =
                                                     let uu____10395 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10395 in
                                                   push_free_var env1 lid
                                                     vname uu____10393 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10392)
                                             | uu____10398 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10403 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10403 in
                                                 let name_tok_corr =
                                                   let uu____10405 =
                                                     let uu____10409 =
                                                       let uu____10410 =
                                                         let uu____10416 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10416) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10410 in
                                                     (uu____10409,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Term.Assume
                                                     uu____10405 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10383 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10345 with
                                      | (decls2,env2) ->
                                          let uu____10440 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10445 =
                                              encode_term res_t1 env' in
                                            match uu____10445 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10453 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10453,
                                                  decls) in
                                          (match uu____10440 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10461 =
                                                   let uu____10465 =
                                                     let uu____10466 =
                                                       let uu____10472 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10472) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10466 in
                                                   (uu____10465,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____10461 in
                                               let freshness =
                                                 let uu____10481 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10481
                                                 then
                                                   let uu____10484 =
                                                     let uu____10485 =
                                                       let uu____10491 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10497 =
                                                         varops.next_id () in
                                                       (vname, uu____10491,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10497) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10485 in
                                                   let uu____10499 =
                                                     let uu____10501 =
                                                       pretype_axiom vapp
                                                         vars in
                                                     [uu____10501] in
                                                   uu____10484 :: uu____10499
                                                 else [] in
                                               let g =
                                                 let uu____10505 =
                                                   let uu____10507 =
                                                     let uu____10509 =
                                                       let uu____10511 =
                                                         let uu____10513 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10513 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10511 in
                                                     FStar_List.append decls3
                                                       uu____10509 in
                                                   FStar_List.append decls2
                                                     uu____10507 in
                                                 FStar_List.append decls11
                                                   uu____10505 in
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
          let uu____10535 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10535 with
          | None  ->
              let uu____10558 = encode_free_var env x t t_norm [] in
              (match uu____10558 with
               | (decls,env1) ->
                   let uu____10573 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10573 with
                    | (n1,x',uu____10592) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10604) -> ((n1, x1), [], env)
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
          let uu____10637 = encode_free_var env lid t tt quals in
          match uu____10637 with
          | (decls,env1) ->
              let uu____10648 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10648
              then
                let uu____10652 =
                  let uu____10654 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10654 in
                (uu____10652, env1)
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
             (fun uu____10682  ->
                fun lb  ->
                  match uu____10682 with
                  | (decls,env1) ->
                      let uu____10694 =
                        let uu____10698 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10698
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10694 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10712 = FStar_Syntax_Util.head_and_args t in
    match uu____10712 with
    | (hd1,args) ->
        let uu____10738 =
          let uu____10739 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10739.FStar_Syntax_Syntax.n in
        (match uu____10738 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10743,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10756 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10771  ->
      fun quals  ->
        match uu____10771 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10820 = FStar_Util.first_N nbinders formals in
              match uu____10820 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10860  ->
                         fun uu____10861  ->
                           match (uu____10860, uu____10861) with
                           | ((formal,uu____10871),(binder,uu____10873)) ->
                               let uu____10878 =
                                 let uu____10883 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10883) in
                               FStar_Syntax_Syntax.NT uu____10878) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10888 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10902  ->
                              match uu____10902 with
                              | (x,i) ->
                                  let uu____10909 =
                                    let uu___155_10910 = x in
                                    let uu____10911 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___155_10910.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___155_10910.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10911
                                    } in
                                  (uu____10909, i))) in
                    FStar_All.pipe_right uu____10888
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10923 =
                      let uu____10925 =
                        let uu____10926 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10926.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10925 in
                    let uu____10930 =
                      let uu____10931 = FStar_Syntax_Subst.compress body in
                      let uu____10932 =
                        let uu____10933 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10933 in
                      FStar_Syntax_Syntax.extend_app_n uu____10931
                        uu____10932 in
                    uu____10930 uu____10923 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10975 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10975
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___156_10976 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___156_10976.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___156_10976.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___156_10976.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___156_10976.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___156_10976.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___156_10976.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___156_10976.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___156_10976.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___156_10976.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___156_10976.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___156_10976.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___156_10976.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___156_10976.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___156_10976.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___156_10976.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___156_10976.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___156_10976.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___156_10976.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___156_10976.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___156_10976.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___156_10976.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___156_10976.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___156_10976.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____10997 = FStar_Syntax_Util.abs_formals e in
                match uu____10997 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11046::uu____11047 ->
                         let uu____11055 =
                           let uu____11056 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11056.FStar_Syntax_Syntax.n in
                         (match uu____11055 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11083 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11083 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11109 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11109
                                   then
                                     let uu____11127 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11127 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11173  ->
                                                   fun uu____11174  ->
                                                     match (uu____11173,
                                                             uu____11174)
                                                     with
                                                     | ((x,uu____11184),
                                                        (b,uu____11186)) ->
                                                         let uu____11191 =
                                                           let uu____11196 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11196) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11191)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11198 =
                                            let uu____11209 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11209) in
                                          (uu____11198, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11244 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11244 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11296) ->
                              let uu____11301 =
                                let uu____11312 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11312 in
                              (uu____11301, true)
                          | uu____11345 when Prims.op_Negation norm1 ->
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
                          | uu____11347 ->
                              let uu____11348 =
                                let uu____11349 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11350 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11349
                                  uu____11350 in
                              failwith uu____11348)
                     | uu____11363 ->
                         let uu____11364 =
                           let uu____11365 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11365.FStar_Syntax_Syntax.n in
                         (match uu____11364 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11392 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11392 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11410 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11410 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11458 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11486 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11486
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11493 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11534  ->
                            fun lb  ->
                              match uu____11534 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11585 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11585
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11588 =
                                      let uu____11596 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11596
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11588 with
                                    | (tok,decl,env2) ->
                                        let uu____11621 =
                                          let uu____11628 =
                                            let uu____11634 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11634, tok) in
                                          uu____11628 :: toks in
                                        (uu____11621, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11493 with
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
                        | uu____11736 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11741 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11741 vars)
                            else
                              (let uu____11743 =
                                 let uu____11747 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11747) in
                               FStar_SMTEncoding_Util.mkApp uu____11743) in
                      let uu____11752 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___125_11754  ->
                                 match uu___125_11754 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11755 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11758 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11758))) in
                      if uu____11752
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11778;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11780;
                                FStar_Syntax_Syntax.lbeff = uu____11781;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11822 =
                                 FStar_Syntax_Subst.univ_var_opening uvs in
                               (match uu____11822 with
                                | (univ_subst,univ_vars1) ->
                                    let env' =
                                      let uu___159_11837 = env1 in
                                      let uu____11838 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1.tcenv univ_vars1 in
                                      {
                                        bindings = (uu___159_11837.bindings);
                                        depth = (uu___159_11837.depth);
                                        tcenv = uu____11838;
                                        warn = (uu___159_11837.warn);
                                        cache = (uu___159_11837.cache);
                                        nolabels = (uu___159_11837.nolabels);
                                        use_zfuel_name =
                                          (uu___159_11837.use_zfuel_name);
                                        encode_non_total_function_typ =
                                          (uu___159_11837.encode_non_total_function_typ)
                                      } in
                                    let t_norm1 =
                                      FStar_Syntax_Subst.subst univ_subst
                                        t_norm in
                                    let e1 =
                                      let uu____11841 =
                                        FStar_Syntax_Subst.subst univ_subst e in
                                      FStar_Syntax_Subst.compress uu____11841 in
                                    let uu____11842 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11842 with
                                     | ((binders,body,uu____11854,uu____11855),curry)
                                         ->
                                         ((let uu____11862 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11862
                                           then
                                             let uu____11863 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11864 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11863 uu____11864
                                           else ());
                                          (let uu____11866 =
                                             encode_binders None binders env' in
                                           match uu____11866 with
                                           | (vars,guards,env'1,binder_decls,uu____11882)
                                               ->
                                               let body1 =
                                                 let uu____11890 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11890
                                                 then
                                                   reify_body env'1.tcenv
                                                     body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11893 =
                                                 let uu____11898 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11898
                                                 then
                                                   let uu____11904 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11905 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11904, uu____11905)
                                                 else
                                                   (let uu____11911 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11911)) in
                                               (match uu____11893 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11925 =
                                                        let uu____11929 =
                                                          let uu____11930 =
                                                            let uu____11936 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11936) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11930 in
                                                        let uu____11942 =
                                                          let uu____11944 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11944 in
                                                        (uu____11929,
                                                          uu____11942,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Term.Assume
                                                        uu____11925 in
                                                    let uu____11946 =
                                                      let uu____11948 =
                                                        let uu____11950 =
                                                          let uu____11952 =
                                                            let uu____11954 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11954 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11952 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11950 in
                                                      FStar_List.append
                                                        decls1 uu____11948 in
                                                    (uu____11946, env1))))))
                           | uu____11957 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11976 = varops.fresh "fuel" in
                             (uu____11976, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____11979 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12018  ->
                                     fun uu____12019  ->
                                       match (uu____12018, uu____12019) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12101 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12101 in
                                           let gtok =
                                             let uu____12103 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12103 in
                                           let env3 =
                                             let uu____12105 =
                                               let uu____12107 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12107 in
                                             push_free_var env2 flid gtok
                                               uu____12105 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____11979 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12191
                                 t_norm uu____12193 =
                                 match (uu____12191, uu____12193) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12218;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12219;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12236 =
                                       FStar_Syntax_Subst.univ_var_opening
                                         uvs in
                                     (match uu____12236 with
                                      | (univ_subst,univ_vars1) ->
                                          let env' =
                                            let uu___160_12253 = env2 in
                                            let uu____12254 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env2.tcenv univ_vars1 in
                                            {
                                              bindings =
                                                (uu___160_12253.bindings);
                                              depth = (uu___160_12253.depth);
                                              tcenv = uu____12254;
                                              warn = (uu___160_12253.warn);
                                              cache = (uu___160_12253.cache);
                                              nolabels =
                                                (uu___160_12253.nolabels);
                                              use_zfuel_name =
                                                (uu___160_12253.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___160_12253.encode_non_total_function_typ)
                                            } in
                                          let t_norm1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst t_norm in
                                          let e1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst e in
                                          ((let uu____12258 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12258
                                            then
                                              let uu____12259 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12260 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12261 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12259 uu____12260
                                                uu____12261
                                            else ());
                                           (let uu____12263 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12263 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12285 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12285
                                                  then
                                                    let uu____12286 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12287 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12288 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12289 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12286 uu____12287
                                                      uu____12288 uu____12289
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12293 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12293 with
                                                  | (vars,guards,env'1,binder_decls,uu____12311)
                                                      ->
                                                      let decl_g =
                                                        let uu____12319 =
                                                          let uu____12325 =
                                                            let uu____12327 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12327 in
                                                          (g, uu____12325,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12319 in
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
                                                        let uu____12342 =
                                                          let uu____12346 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12346) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12342 in
                                                      let gsapp =
                                                        let uu____12352 =
                                                          let uu____12356 =
                                                            let uu____12358 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12358 ::
                                                              vars_tm in
                                                          (g, uu____12356) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12352 in
                                                      let gmax =
                                                        let uu____12362 =
                                                          let uu____12366 =
                                                            let uu____12368 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12368 ::
                                                              vars_tm in
                                                          (g, uu____12366) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12362 in
                                                      let body1 =
                                                        let uu____12372 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12372
                                                        then
                                                          reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12374 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12374 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12385
                                                               =
                                                               let uu____12389
                                                                 =
                                                                 let uu____12390
                                                                   =
                                                                   let uu____12398
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
                                                                    uu____12398) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12390 in
                                                               let uu____12409
                                                                 =
                                                                 let uu____12411
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12411 in
                                                               (uu____12389,
                                                                 uu____12409,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12385 in
                                                           let eqn_f =
                                                             let uu____12414
                                                               =
                                                               let uu____12418
                                                                 =
                                                                 let uu____12419
                                                                   =
                                                                   let uu____12425
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12425) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12419 in
                                                               (uu____12418,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12414 in
                                                           let eqn_g' =
                                                             let uu____12433
                                                               =
                                                               let uu____12437
                                                                 =
                                                                 let uu____12438
                                                                   =
                                                                   let uu____12444
                                                                    =
                                                                    let uu____12445
                                                                    =
                                                                    let uu____12448
                                                                    =
                                                                    let uu____12449
                                                                    =
                                                                    let uu____12453
                                                                    =
                                                                    let uu____12455
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12455
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12453) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12449 in
                                                                    (gsapp,
                                                                    uu____12448) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12445 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12444) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12438 in
                                                               (uu____12437,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12433 in
                                                           let uu____12467 =
                                                             let uu____12472
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12472
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12489)
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
                                                                    let uu____12504
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12504
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12507
                                                                    =
                                                                    let uu____12511
                                                                    =
                                                                    let uu____12512
                                                                    =
                                                                    let uu____12518
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12518) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12512 in
                                                                    (uu____12511,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Term.Assume
                                                                    uu____12507 in
                                                                 let uu____12529
                                                                   =
                                                                   let uu____12533
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12533
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12541
                                                                    =
                                                                    let uu____12543
                                                                    =
                                                                    let uu____12544
                                                                    =
                                                                    let uu____12548
                                                                    =
                                                                    let uu____12549
                                                                    =
                                                                    let uu____12555
                                                                    =
                                                                    let uu____12556
                                                                    =
                                                                    let uu____12559
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12559,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12556 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12555) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12549 in
                                                                    (uu____12548,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12544 in
                                                                    [uu____12543] in
                                                                    (d3,
                                                                    uu____12541) in
                                                                 (match uu____12529
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12467
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
                               let uu____12594 =
                                 let uu____12601 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12633  ->
                                      fun uu____12634  ->
                                        match (uu____12633, uu____12634) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12710 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12710 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12601 in
                               (match uu____12594 with
                                | (decls2,eqns,env01) ->
                                    let uu____12750 =
                                      let isDeclFun uu___126_12758 =
                                        match uu___126_12758 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12759 -> true
                                        | uu____12765 -> false in
                                      let uu____12766 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12766
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12750 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12793 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12793
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
      (let uu____12826 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____12826
       then
         let uu____12827 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
           uu____12827
       else ());
      (let nm =
         let uu____12830 = FStar_Syntax_Util.lid_of_sigelt se in
         match uu____12830 with | None  -> "" | Some l -> l.FStar_Ident.str in
       let uu____12833 = encode_sigelt' env se in
       match uu____12833 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12842 =
                  let uu____12844 =
                    let uu____12845 = FStar_Util.format1 "<Skipped %s/>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12845 in
                  [uu____12844] in
                (uu____12842, e)
            | uu____12847 ->
                let uu____12848 =
                  let uu____12850 =
                    let uu____12852 =
                      let uu____12853 =
                        FStar_Util.format1 "<Start encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12853 in
                    uu____12852 :: g in
                  let uu____12854 =
                    let uu____12856 =
                      let uu____12857 =
                        FStar_Util.format1 "</end encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12857 in
                    [uu____12856] in
                  FStar_List.append uu____12850 uu____12854 in
                (uu____12848, e)))
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12865 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12874 =
            let uu____12875 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12875 Prims.op_Negation in
          if uu____12874
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12895 ->
                   let uu____12896 =
                     let uu____12899 =
                       let uu____12900 =
                         let uu____12915 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12915) in
                       FStar_Syntax_Syntax.Tm_abs uu____12900 in
                     FStar_Syntax_Syntax.mk uu____12899 in
                   uu____12896 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____12968 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____12968 with
               | (aname,atok,env2) ->
                   let uu____12978 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____12978 with
                    | (formals,uu____12988) ->
                        let uu____12995 =
                          let uu____12998 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____12998 env2 in
                        (match uu____12995 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13006 =
                                 let uu____13007 =
                                   let uu____13013 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13021  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13013,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13007 in
                               [uu____13006;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13028 =
                               let aux uu____13057 uu____13058 =
                                 match (uu____13057, uu____13058) with
                                 | ((bv,uu____13085),(env3,acc_sorts,acc)) ->
                                     let uu____13106 = gen_term_var env3 bv in
                                     (match uu____13106 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13028 with
                              | (uu____13144,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13158 =
                                      let uu____13162 =
                                        let uu____13163 =
                                          let uu____13169 =
                                            let uu____13170 =
                                              let uu____13173 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13173) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13170 in
                                          ([[app]], xs_sorts, uu____13169) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13163 in
                                      (uu____13162, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Term.Assume uu____13158 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13185 =
                                      let uu____13189 =
                                        let uu____13190 =
                                          let uu____13196 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13196) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13190 in
                                      (uu____13189,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Term.Assume uu____13185 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13206 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13206 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____13222,uu____13223,uu____13224) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13227 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13227 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13238,t,quals) ->
          let will_encode_definition =
            let uu____13244 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___127_13246  ->
                      match uu___127_13246 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13249 -> false)) in
            Prims.op_Negation uu____13244 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13255 = encode_top_level_val env fv t quals in
             match uu____13255 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13267 =
                   let uu____13269 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13269 in
                 (uu____13267, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____13274) ->
          let uu____13277 = encode_formula f env in
          (match uu____13277 with
           | (f1,decls) ->
               let g =
                 let uu____13286 =
                   let uu____13287 =
                     let uu____13291 =
                       let uu____13293 =
                         let uu____13294 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13294 in
                       Some uu____13293 in
                     let uu____13295 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13291, uu____13295) in
                   FStar_SMTEncoding_Term.Assume uu____13287 in
                 [uu____13286] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13299,quals,uu____13301) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13309 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13316 =
                       let uu____13321 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13321.FStar_Syntax_Syntax.fv_name in
                     uu____13316.FStar_Syntax_Syntax.v in
                   let uu____13325 =
                     let uu____13326 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13326 in
                   if uu____13325
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
                     let uu____13345 = encode_sigelt' env1 val_decl in
                     match uu____13345 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13309 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13362,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13364;
                          FStar_Syntax_Syntax.lbtyp = uu____13365;
                          FStar_Syntax_Syntax.lbeff = uu____13366;
                          FStar_Syntax_Syntax.lbdef = uu____13367;_}::[]),uu____13368,uu____13369,uu____13370)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13386 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13386 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let valid_b2t_x =
                 let uu____13404 =
                   let uu____13408 =
                     let uu____13410 =
                       FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
                     [uu____13410] in
                   ("Valid", uu____13408) in
                 FStar_SMTEncoding_Util.mkApp uu____13404 in
               let decls =
                 let uu____13415 =
                   let uu____13417 =
                     let uu____13418 =
                       let uu____13422 =
                         let uu____13423 =
                           let uu____13429 =
                             let uu____13430 =
                               let uu____13433 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13433) in
                             FStar_SMTEncoding_Util.mkEq uu____13430 in
                           ([[valid_b2t_x]], [xx], uu____13429) in
                         FStar_SMTEncoding_Util.mkForall uu____13423 in
                       (uu____13422, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Term.Assume uu____13418 in
                   [uu____13417] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13415 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let
          (uu____13450,uu____13451,quals,uu____13453) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___128_13461  ->
                  match uu___128_13461 with
                  | FStar_Syntax_Syntax.Discriminator uu____13462 -> true
                  | uu____13463 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13465,lids,quals,uu____13468) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13477 =
                     let uu____13478 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13478.FStar_Ident.idText in
                   uu____13477 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___129_13480  ->
                     match uu___129_13480 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13481 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13484,quals,uu____13486) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___130_13498  ->
                  match uu___130_13498 with
                  | FStar_Syntax_Syntax.Projector uu____13499 -> true
                  | uu____13502 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13509 = try_lookup_free_var env l in
          (match uu____13509 with
           | Some uu____13513 -> ([], env)
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
          ((is_rec,bindings),uu____13522,quals,uu____13524) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13538,uu____13539) ->
          let uu____13546 = encode_signature env ses in
          (match uu____13546 with
           | (g,env1) ->
               let uu____13556 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___131_13566  ->
                         match uu___131_13566 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13567,Some "inversion axiom",uu____13568)
                             -> false
                         | uu____13570 -> true)) in
               (match uu____13556 with
                | (g',inversions) ->
                    let uu____13579 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___132_13589  ->
                              match uu___132_13589 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13590 ->
                                  true
                              | uu____13596 -> false)) in
                    (match uu____13579 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13607,tps,k,uu____13610,datas,quals) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___133_13621  ->
                    match uu___133_13621 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13622 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13629 = c in
              match uu____13629 with
              | (name,args,uu____13633,uu____13634,uu____13635) ->
                  let uu____13638 =
                    let uu____13639 =
                      let uu____13645 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13652  ->
                                match uu____13652 with
                                | (uu____13656,sort,uu____13658) -> sort)) in
                      (name, uu____13645, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13639 in
                  [uu____13638]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13676 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13679 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13679 FStar_Option.isNone)) in
            if uu____13676
            then []
            else
              (let uu____13696 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13696 with
               | (xxsym,xx) ->
                   let uu____13702 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13713  ->
                             fun l  ->
                               match uu____13713 with
                               | (out,decls) ->
                                   let uu____13725 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13725 with
                                    | (uu____13731,data_t) ->
                                        let uu____13733 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13733 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13762 =
                                                 let uu____13763 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13763.FStar_Syntax_Syntax.n in
                                               match uu____13762 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13771,indices) ->
                                                   indices
                                               | uu____13787 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13799  ->
                                                         match uu____13799
                                                         with
                                                         | (x,uu____13803) ->
                                                             let uu____13804
                                                               =
                                                               let uu____13805
                                                                 =
                                                                 let uu____13809
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13809,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13805 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13804)
                                                    env) in
                                             let uu____13811 =
                                               encode_args indices env1 in
                                             (match uu____13811 with
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
                                                      let uu____13831 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13839
                                                                 =
                                                                 let uu____13842
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13842,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13839)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13831
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13844 =
                                                      let uu____13845 =
                                                        let uu____13848 =
                                                          let uu____13849 =
                                                            let uu____13852 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13852,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13849 in
                                                        (out, uu____13848) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13845 in
                                                    (uu____13844,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13702 with
                    | (data_ax,decls) ->
                        let uu____13860 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13860 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13871 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13871 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13874 =
                                 let uu____13878 =
                                   let uu____13879 =
                                     let uu____13885 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13893 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13885,
                                       uu____13893) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13879 in
                                 let uu____13901 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13878, (Some "inversion axiom"),
                                   uu____13901) in
                               FStar_SMTEncoding_Term.Assume uu____13874 in
                             let pattern_guarded_inversion =
                               let uu____13905 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13905
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13913 =
                                   let uu____13914 =
                                     let uu____13918 =
                                       let uu____13919 =
                                         let uu____13925 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13933 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13925, uu____13933) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13919 in
                                     let uu____13941 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13918, (Some "inversion axiom"),
                                       uu____13941) in
                                   FStar_SMTEncoding_Term.Assume uu____13914 in
                                 [uu____13913]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13944 =
            let uu____13952 =
              let uu____13953 = FStar_Syntax_Subst.compress k in
              uu____13953.FStar_Syntax_Syntax.n in
            match uu____13952 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13982 -> (tps, k) in
          (match uu____13944 with
           | (formals,res) ->
               let uu____13997 = FStar_Syntax_Subst.open_term formals res in
               (match uu____13997 with
                | (formals1,res1) ->
                    let uu____14004 = encode_binders None formals1 env in
                    (match uu____14004 with
                     | (vars,guards,env',binder_decls,uu____14019) ->
                         let uu____14026 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14026 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14039 =
                                  let uu____14043 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14043) in
                                FStar_SMTEncoding_Util.mkApp uu____14039 in
                              let uu____14048 =
                                let tname_decl =
                                  let uu____14054 =
                                    let uu____14055 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14070  ->
                                              match uu____14070 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14078 = varops.next_id () in
                                    (tname, uu____14055,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14078, false) in
                                  constructor_or_logic_type_decl uu____14054 in
                                let uu____14083 =
                                  match vars with
                                  | [] ->
                                      let uu____14090 =
                                        let uu____14091 =
                                          let uu____14093 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14093 in
                                        push_free_var env1 t tname
                                          uu____14091 in
                                      ([], uu____14090)
                                  | uu____14097 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14103 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14103 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14112 =
                                          let uu____14116 =
                                            let uu____14117 =
                                              let uu____14125 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14125) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14117 in
                                          (uu____14116,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____14112 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14083 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14048 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14148 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14148 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14162 =
                                               let uu____14163 =
                                                 let uu____14167 =
                                                   let uu____14168 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14168 in
                                                 (uu____14167,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14163 in
                                             [uu____14162]
                                           else [] in
                                         let uu____14171 =
                                           let uu____14173 =
                                             let uu____14175 =
                                               let uu____14176 =
                                                 let uu____14180 =
                                                   let uu____14181 =
                                                     let uu____14187 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14187) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14181 in
                                                 (uu____14180, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14176 in
                                             [uu____14175] in
                                           FStar_List.append karr uu____14173 in
                                         FStar_List.append decls1 uu____14171 in
                                   let aux =
                                     let uu____14196 =
                                       let uu____14198 =
                                         inversion_axioms tapp vars in
                                       let uu____14200 =
                                         let uu____14202 =
                                           pretype_axiom tapp vars in
                                         [uu____14202] in
                                       FStar_List.append uu____14198
                                         uu____14200 in
                                     FStar_List.append kindingAx uu____14196 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14207,uu____14208,uu____14209,uu____14210,uu____14211,uu____14212)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14219,t,uu____14221,n_tps,quals,uu____14224) ->
          let uu____14229 = new_term_constant_and_tok_from_lid env d in
          (match uu____14229 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14240 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14240 with
                | (formals,t_res) ->
                    let uu____14262 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14262 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14271 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14271 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14309 =
                                            mk_term_projector_name d x in
                                          (uu____14309,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14311 =
                                  let uu____14321 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14321, true) in
                                FStar_All.pipe_right uu____14311
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
                              let uu____14343 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14343 with
                               | (tok_typing,decls3) ->
                                   let uu____14350 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14350 with
                                    | (vars',guards',env'',decls_formals,uu____14365)
                                        ->
                                        let uu____14372 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14372 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14391 ->
                                                   let uu____14395 =
                                                     let uu____14396 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14396 in
                                                   [uu____14395] in
                                             let encode_elim uu____14403 =
                                               let uu____14404 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14404 with
                                               | (head1,args) ->
                                                   let uu____14433 =
                                                     let uu____14434 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14434.FStar_Syntax_Syntax.n in
                                                   (match uu____14433 with
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
                                                        let uu____14452 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14452
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
                                                                 | uu____14478
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14486
                                                                    =
                                                                    let uu____14487
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14487 in
                                                                    if
                                                                    uu____14486
                                                                    then
                                                                    let uu____14494
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14494]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14496
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14509
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14509
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14531
                                                                    =
                                                                    let uu____14535
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14535 in
                                                                    (match uu____14531
                                                                    with
                                                                    | 
                                                                    (uu____14542,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14548
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14548
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14550
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14550
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
                                                             (match uu____14496
                                                              with
                                                              | (uu____14558,arg_vars,elim_eqns_or_guards,uu____14561)
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
                                                                    let uu____14580
                                                                    =
                                                                    let uu____14584
                                                                    =
                                                                    let uu____14585
                                                                    =
                                                                    let uu____14591
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14597
                                                                    =
                                                                    let uu____14598
                                                                    =
                                                                    let uu____14601
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14601) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14598 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14591,
                                                                    uu____14597) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14585 in
                                                                    (uu____14584,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14580 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14614
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14614,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14616
                                                                    =
                                                                    let uu____14620
                                                                    =
                                                                    let uu____14621
                                                                    =
                                                                    let uu____14627
                                                                    =
                                                                    let uu____14630
                                                                    =
                                                                    let uu____14632
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14632] in
                                                                    [uu____14630] in
                                                                    let uu____14635
                                                                    =
                                                                    let uu____14636
                                                                    =
                                                                    let uu____14639
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14640
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14639,
                                                                    uu____14640) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14636 in
                                                                    (uu____14627,
                                                                    [x],
                                                                    uu____14635) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14621 in
                                                                    let uu____14650
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14620,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14650) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14616
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14655
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
                                                                    (let uu____14670
                                                                    =
                                                                    let uu____14671
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14671
                                                                    dapp1 in
                                                                    [uu____14670]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14655
                                                                    FStar_List.flatten in
                                                                    let uu____14675
                                                                    =
                                                                    let uu____14679
                                                                    =
                                                                    let uu____14680
                                                                    =
                                                                    let uu____14686
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14692
                                                                    =
                                                                    let uu____14693
                                                                    =
                                                                    let uu____14696
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14696) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14693 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14686,
                                                                    uu____14692) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14680 in
                                                                    (uu____14679,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14675) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14706 ->
                                                        ((let uu____14708 =
                                                            let uu____14709 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14710 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14709
                                                              uu____14710 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14708);
                                                         ([], []))) in
                                             let uu____14713 = encode_elim () in
                                             (match uu____14713 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14725 =
                                                      let uu____14727 =
                                                        let uu____14729 =
                                                          let uu____14731 =
                                                            let uu____14733 =
                                                              let uu____14734
                                                                =
                                                                let uu____14740
                                                                  =
                                                                  let uu____14742
                                                                    =
                                                                    let uu____14743
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14743 in
                                                                  Some
                                                                    uu____14742 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14740) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14734 in
                                                            [uu____14733] in
                                                          let uu____14746 =
                                                            let uu____14748 =
                                                              let uu____14750
                                                                =
                                                                let uu____14752
                                                                  =
                                                                  let uu____14754
                                                                    =
                                                                    let uu____14756
                                                                    =
                                                                    let uu____14758
                                                                    =
                                                                    let uu____14759
                                                                    =
                                                                    let uu____14763
                                                                    =
                                                                    let uu____14764
                                                                    =
                                                                    let uu____14770
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14770) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14764 in
                                                                    (uu____14763,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14759 in
                                                                    let uu____14777
                                                                    =
                                                                    let uu____14779
                                                                    =
                                                                    let uu____14780
                                                                    =
                                                                    let uu____14784
                                                                    =
                                                                    let uu____14785
                                                                    =
                                                                    let uu____14791
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14797
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14791,
                                                                    uu____14797) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14785 in
                                                                    (uu____14784,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14780 in
                                                                    [uu____14779] in
                                                                    uu____14758
                                                                    ::
                                                                    uu____14777 in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14756 in
                                                                  FStar_List.append
                                                                    uu____14754
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14752 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14750 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14748 in
                                                          FStar_List.append
                                                            uu____14731
                                                            uu____14746 in
                                                        FStar_List.append
                                                          decls3 uu____14729 in
                                                      FStar_List.append
                                                        decls2 uu____14727 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14725 in
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
           (fun uu____14818  ->
              fun se  ->
                match uu____14818 with
                | (g,env1) ->
                    let uu____14830 = encode_sigelt env1 se in
                    (match uu____14830 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14866 =
        match uu____14866 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14884 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14889 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14889
                   then
                     let uu____14890 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14891 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14892 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14890 uu____14891 uu____14892
                   else ());
                  (let uu____14894 = encode_term t1 env1 in
                   match uu____14894 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14904 =
                         let uu____14908 =
                           let uu____14909 =
                             let uu____14910 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____14910
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____14909 in
                         new_term_constant_from_string env1 x uu____14908 in
                       (match uu____14904 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____14921 = FStar_Options.log_queries () in
                              if uu____14921
                              then
                                let uu____14923 =
                                  let uu____14924 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____14925 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____14926 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14924 uu____14925 uu____14926 in
                                Some uu____14923
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14937,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____14946 = encode_free_var env1 fv t t_norm [] in
                 (match uu____14946 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____14965 = encode_sigelt env1 se in
                 (match uu____14965 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____14975 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____14975 with | (uu____14987,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15032  ->
            match uu____15032 with
            | (l,uu____15039,uu____15040) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15061  ->
            match uu____15061 with
            | (l,uu____15069,uu____15070) ->
                let uu____15075 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____15076 =
                  let uu____15078 =
                    let uu____15079 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15079 in
                  [uu____15078] in
                uu____15075 :: uu____15076)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15090 =
      let uu____15092 =
        let uu____15093 = FStar_Util.smap_create (Prims.parse_int "100") in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15093;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true
        } in
      [uu____15092] in
    FStar_ST.write last_env uu____15090
let get_env: FStar_TypeChecker_Env.env -> env_t =
  fun tcenv  ->
    let uu____15111 = FStar_ST.read last_env in
    match uu____15111 with
    | [] -> failwith "No env; call init first!"
    | e::uu____15117 ->
        let uu___161_15119 = e in
        {
          bindings = (uu___161_15119.bindings);
          depth = (uu___161_15119.depth);
          tcenv;
          warn = (uu___161_15119.warn);
          cache = (uu___161_15119.cache);
          nolabels = (uu___161_15119.nolabels);
          use_zfuel_name = (uu___161_15119.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___161_15119.encode_non_total_function_typ)
        }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15123 = FStar_ST.read last_env in
    match uu____15123 with
    | [] -> failwith "Empty env stack"
    | uu____15128::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15136  ->
    let uu____15137 = FStar_ST.read last_env in
    match uu____15137 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___162_15158 = hd1 in
          {
            bindings = (uu___162_15158.bindings);
            depth = (uu___162_15158.depth);
            tcenv = (uu___162_15158.tcenv);
            warn = (uu___162_15158.warn);
            cache = refs;
            nolabels = (uu___162_15158.nolabels);
            use_zfuel_name = (uu___162_15158.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_15158.encode_non_total_function_typ)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15164  ->
    let uu____15165 = FStar_ST.read last_env in
    match uu____15165 with
    | [] -> failwith "Popping an empty stack"
    | uu____15170::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15178  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15181  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15184  ->
    let uu____15185 = FStar_ST.read last_env in
    match uu____15185 with
    | hd1::uu____15191::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15197 -> failwith "Impossible"
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
        let uu____15242 = FStar_Options.log_queries () in
        if uu____15242
        then
          let uu____15244 =
            let uu____15245 =
              let uu____15246 =
                let uu____15247 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15247 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15246 in
            FStar_SMTEncoding_Term.Caption uu____15245 in
          uu____15244 :: decls
        else decls in
      let env = get_env tcenv in
      let uu____15254 = encode_sigelt env se in
      match uu____15254 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15260 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15260))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15271 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15271
       then
         let uu____15272 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15272
       else ());
      (let env = get_env tcenv in
       let uu____15277 =
         encode_signature
           (let uu___163_15281 = env in
            {
              bindings = (uu___163_15281.bindings);
              depth = (uu___163_15281.depth);
              tcenv = (uu___163_15281.tcenv);
              warn = false;
              cache = (uu___163_15281.cache);
              nolabels = (uu___163_15281.nolabels);
              use_zfuel_name = (uu___163_15281.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___163_15281.encode_non_total_function_typ)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15277 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15293 = FStar_Options.log_queries () in
             if uu____15293
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___164_15298 = env1 in
               {
                 bindings = (uu___164_15298.bindings);
                 depth = (uu___164_15298.depth);
                 tcenv = (uu___164_15298.tcenv);
                 warn = true;
                 cache = (uu___164_15298.cache);
                 nolabels = (uu___164_15298.nolabels);
                 use_zfuel_name = (uu___164_15298.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___164_15298.encode_non_total_function_typ)
               });
            (let uu____15300 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15300
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
        (let uu____15335 =
           let uu____15336 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15336.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15335);
        (let env = get_env tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15344 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15365 = aux rest in
                 (match uu____15365 with
                  | (out,rest1) ->
                      let t =
                        let uu____15383 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15383 with
                        | Some uu____15387 ->
                            let uu____15388 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15388
                              x.FStar_Syntax_Syntax.sort
                        | uu____15389 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15392 =
                        let uu____15394 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___165_15395 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___165_15395.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___165_15395.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15394 :: out in
                      (uu____15392, rest1))
             | uu____15398 -> ([], bindings1) in
           let uu____15402 = aux bindings in
           match uu____15402 with
           | (closing,bindings1) ->
               let uu____15416 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15416, bindings1) in
         match uu____15344 with
         | (q1,bindings1) ->
             let uu____15429 =
               let uu____15432 =
                 FStar_List.filter
                   (fun uu___134_15434  ->
                      match uu___134_15434 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15435 ->
                          false
                      | uu____15439 -> true) bindings1 in
               encode_env_bindings env uu____15432 in
             (match uu____15429 with
              | (env_decls,env1) ->
                  ((let uu____15450 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15450
                    then
                      let uu____15451 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15451
                    else ());
                   (let uu____15453 = encode_formula q1 env1 in
                    match uu____15453 with
                    | (phi,qdecls) ->
                        let uu____15465 =
                          let uu____15468 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15468 phi in
                        (match uu____15465 with
                         | (labels,phi1) ->
                             let uu____15478 = encode_labels labels in
                             (match uu____15478 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15499 =
                                      let uu____15503 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15504 =
                                        varops.mk_unique "@query" in
                                      (uu____15503, (Some "query"),
                                        uu____15504) in
                                    FStar_SMTEncoding_Term.Assume uu____15499 in
                                  let suffix =
                                    let uu____15508 =
                                      let uu____15510 =
                                        let uu____15512 =
                                          FStar_Options.print_z3_statistics
                                            () in
                                        if uu____15512
                                        then
                                          [FStar_SMTEncoding_Term.PrintStats]
                                        else [] in
                                      FStar_List.append uu____15510
                                        [FStar_SMTEncoding_Term.Echo "Done!"] in
                                    FStar_List.append label_suffix
                                      uu____15508 in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env = get_env tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15525 = encode_formula q env in
       match uu____15525 with
       | (f,uu____15529) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15531) -> true
             | uu____15534 -> false)))