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
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_'
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___135_98 = a in
        let uu____99 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____99;
          FStar_Syntax_Syntax.index = (uu___135_98.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___135_98.FStar_Syntax_Syntax.sort)
        } in
      let uu____100 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____100
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____113 =
          let uu____114 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____114 in
        let uu____115 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____115 with
        | (uu____118,t) ->
            let uu____120 =
              let uu____121 = FStar_Syntax_Subst.compress t in
              uu____121.FStar_Syntax_Syntax.n in
            (match uu____120 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____136 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____136 with
                  | (binders,uu____140) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid (Prims.fst b)))
             | uu____151 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____158 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____158
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____165 =
        let uu____168 = mk_term_projector_name lid a in
        (uu____168,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____165
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____175 =
        let uu____178 = mk_term_projector_name_by_pos lid i in
        (uu____178,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____175
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
  let new_scope uu____368 =
    let uu____369 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____371 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____369, uu____371) in
  let scopes =
    let uu____382 = let uu____388 = new_scope () in [uu____388] in
    FStar_Util.mk_ref uu____382 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____413 =
        let uu____415 = FStar_ST.read scopes in
        FStar_Util.find_map uu____415
          (fun uu____432  ->
             match uu____432 with
             | (names1,uu____439) -> FStar_Util.smap_try_find names1 y1) in
      match uu____413 with
      | None  -> y1
      | Some uu____444 ->
          (FStar_Util.incr ctr;
           (let uu____449 =
              let uu____450 =
                let uu____451 = FStar_ST.read ctr in
                Prims.string_of_int uu____451 in
              Prims.strcat "__" uu____450 in
            Prims.strcat y1 uu____449)) in
    let top_scope =
      let uu____456 =
        let uu____461 = FStar_ST.read scopes in FStar_List.hd uu____461 in
      FStar_All.pipe_left Prims.fst uu____456 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____500 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____511 =
      let uu____512 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____512 in
    FStar_Util.format2 "%s_%s" pfx uu____511 in
  let string_const s =
    let uu____517 =
      let uu____519 = FStar_ST.read scopes in
      FStar_Util.find_map uu____519
        (fun uu____536  ->
           match uu____536 with
           | (uu____542,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____517 with
    | Some f -> f
    | None  ->
        let id = next_id1 () in
        let f =
          let uu____551 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____551 in
        let top_scope =
          let uu____554 =
            let uu____559 = FStar_ST.read scopes in FStar_List.hd uu____559 in
          FStar_All.pipe_left Prims.snd uu____554 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____587 =
    let uu____588 =
      let uu____594 = new_scope () in
      let uu____599 = FStar_ST.read scopes in uu____594 :: uu____599 in
    FStar_ST.write scopes uu____588 in
  let pop1 uu____626 =
    let uu____627 =
      let uu____633 = FStar_ST.read scopes in FStar_List.tl uu____633 in
    FStar_ST.write scopes uu____627 in
  let mark1 uu____660 = push1 () in
  let reset_mark1 uu____664 = pop1 () in
  let commit_mark1 uu____668 =
    let uu____669 = FStar_ST.read scopes in
    match uu____669 with
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
    | uu____729 -> failwith "Impossible" in
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
    let uu___136_738 = x in
    let uu____739 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____739;
      FStar_Syntax_Syntax.index = (uu___136_738.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___136_738.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term Prims.option* FStar_SMTEncoding_Term.term
  Prims.option)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____760 -> false
let __proj__Binding_var__item___0:
  binding -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____784 -> false
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
    let uu____903 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___112_907  ->
              match uu___112_907 with
              | Binding_var (x,uu____909) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____911,uu____912,uu____913) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____903 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option
  =
  fun env  ->
    fun t  ->
      let uu____946 = FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____946
      then
        let uu____948 = FStar_Syntax_Print.term_to_string t in Some uu____948
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____959 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____959)
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
        (let uu___137_971 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___137_971.tcenv);
           warn = (uu___137_971.warn);
           cache = (uu___137_971.cache);
           nolabels = (uu___137_971.nolabels);
           use_zfuel_name = (uu___137_971.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___137_971.encode_non_total_function_typ)
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
        (let uu___138_984 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___138_984.depth);
           tcenv = (uu___138_984.tcenv);
           warn = (uu___138_984.warn);
           cache = (uu___138_984.cache);
           nolabels = (uu___138_984.nolabels);
           use_zfuel_name = (uu___138_984.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___138_984.encode_non_total_function_typ)
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
          (let uu___139_1000 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___139_1000.depth);
             tcenv = (uu___139_1000.tcenv);
             warn = (uu___139_1000.warn);
             cache = (uu___139_1000.cache);
             nolabels = (uu___139_1000.nolabels);
             use_zfuel_name = (uu___139_1000.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___139_1000.encode_non_total_function_typ)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___140_1010 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___140_1010.depth);
          tcenv = (uu___140_1010.tcenv);
          warn = (uu___140_1010.warn);
          cache = (uu___140_1010.cache);
          nolabels = (uu___140_1010.nolabels);
          use_zfuel_name = (uu___140_1010.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___140_1010.encode_non_total_function_typ)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___113_1026  ->
             match uu___113_1026 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1034 -> None) in
      let uu____1037 = aux a in
      match uu____1037 with
      | None  ->
          let a2 = unmangle a in
          let uu____1044 = aux a2 in
          (match uu____1044 with
           | None  ->
               let uu____1050 =
                 let uu____1051 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1052 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1051 uu____1052 in
               failwith uu____1050
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1072 =
        let uu___141_1073 = env in
        let uu____1074 =
          let uu____1076 =
            let uu____1077 =
              let uu____1084 =
                let uu____1086 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1086 in
              (x, fname, uu____1084, None) in
            Binding_fvar uu____1077 in
          uu____1076 :: (env.bindings) in
        {
          bindings = uu____1074;
          depth = (uu___141_1073.depth);
          tcenv = (uu___141_1073.tcenv);
          warn = (uu___141_1073.warn);
          cache = (uu___141_1073.cache);
          nolabels = (uu___141_1073.nolabels);
          use_zfuel_name = (uu___141_1073.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___141_1073.encode_non_total_function_typ)
        } in
      (fname, ftok, uu____1072)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___114_1108  ->
           match uu___114_1108 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1130 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1142 =
        lookup_binding env
          (fun uu___115_1144  ->
             match uu___115_1144 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1154 -> None) in
      FStar_All.pipe_right uu____1142 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1167 = try_lookup_lid env a in
      match uu____1167 with
      | None  ->
          let uu____1184 =
            let uu____1185 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1185 in
          failwith uu____1184
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
          let uu___142_1216 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___142_1216.depth);
            tcenv = (uu___142_1216.tcenv);
            warn = (uu___142_1216.warn);
            cache = (uu___142_1216.cache);
            nolabels = (uu___142_1216.nolabels);
            use_zfuel_name = (uu___142_1216.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___142_1216.encode_non_total_function_typ)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1228 = lookup_lid env x in
        match uu____1228 with
        | (t1,t2,uu____1236) ->
            let t3 =
              let uu____1242 =
                let uu____1246 =
                  let uu____1248 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1248] in
                (f, uu____1246) in
              FStar_SMTEncoding_Util.mkApp uu____1242 in
            let uu___143_1251 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___143_1251.depth);
              tcenv = (uu___143_1251.tcenv);
              warn = (uu___143_1251.warn);
              cache = (uu___143_1251.cache);
              nolabels = (uu___143_1251.nolabels);
              use_zfuel_name = (uu___143_1251.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___143_1251.encode_non_total_function_typ)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1261 = try_lookup_lid env l in
      match uu____1261 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1288 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1293,fuel::[]) ->
                         let uu____1296 =
                           let uu____1297 =
                             let uu____1298 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1298 Prims.fst in
                           FStar_Util.starts_with uu____1297 "fuel" in
                         if uu____1296
                         then
                           let uu____1300 =
                             let uu____1301 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1301
                               fuel in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1300
                         else Some t
                     | uu____1304 -> Some t)
                | uu____1305 -> None))
let lookup_free_var env a =
  let uu____1323 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1323 with
  | Some t -> t
  | None  ->
      let uu____1326 =
        let uu____1327 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1327 in
      failwith uu____1326
let lookup_free_var_name env a =
  let uu____1344 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1344 with | (x,uu____1351,uu____1352) -> x
let lookup_free_var_sym env a =
  let uu____1376 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1376 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1397;
             FStar_SMTEncoding_Term.rng = uu____1398;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1406 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1420 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___116_1429  ->
           match uu___116_1429 with
           | Binding_fvar (uu____1431,nm',tok,uu____1434) when nm = nm' ->
               tok
           | uu____1439 -> None)
let mkForall_fuel' n1 uu____1456 =
  match uu____1456 with
  | (pats,vars,body) ->
      let fallback uu____1472 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1475 = FStar_Options.unthrottle_inductives () in
      if uu____1475
      then fallback ()
      else
        (let uu____1477 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1477 with
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
                       | uu____1496 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1510 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1510
                     | uu____1512 ->
                         let uu____1513 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1513 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1516 -> body in
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
          let uu____1560 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1560 FStar_Option.isNone
      | uu____1573 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1580 =
        let uu____1581 = FStar_Syntax_Util.un_uinst t in
        uu____1581.FStar_Syntax_Syntax.n in
      match uu____1580 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1584,uu____1585,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___117_1614  ->
                  match uu___117_1614 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1615 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1616,uu____1617,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1644 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1644 FStar_Option.isSome
      | uu____1657 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1664 = head_normal env t in
      if uu____1664
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
    let uu____1675 =
      let uu____1679 = FStar_Syntax_Syntax.null_binder t in [uu____1679] in
    let uu____1680 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1675 uu____1680 None
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
                    let uu____1707 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1707
                | s ->
                    let uu____1710 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1710) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___118_1722  ->
    match uu___118_1722 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1723 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____1751;
                       FStar_SMTEncoding_Term.rng = uu____1752;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              aux f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1766) ->
              let uu____1771 =
                ((FStar_List.length args) = (FStar_List.length vars)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1781 -> false) args vars) in
              if uu____1771 then tok_of_name env f else None
          | (uu____1784,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t1 in
              let uu____1787 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1789 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1789)) in
              if uu____1787 then Some t1 else None
          | uu____1792 -> None in
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
      (let uu____1807 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____1807
       then
         let uu____1808 = FStar_Syntax_Print.term_to_string tm in
         let uu____1809 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____1808 uu____1809
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
    | uu____1891 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___119_1894  ->
    match uu___119_1894 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____1896 =
          let uu____1900 =
            let uu____1902 =
              let uu____1903 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____1903 in
            [uu____1902] in
          ("FStar.Char.Char", uu____1900) in
        FStar_SMTEncoding_Util.mkApp uu____1896
    | FStar_Const.Const_int (i,None ) ->
        let uu____1911 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____1911
    | FStar_Const.Const_int (i,Some uu____1913) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____1922) ->
        let uu____1925 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____1925
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____1929 =
          let uu____1930 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____1930 in
        failwith uu____1929
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1949 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1957 ->
            let uu____1962 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____1962
        | uu____1963 ->
            if norm1
            then let uu____1964 = whnf env t1 in aux false uu____1964
            else
              (let uu____1966 =
                 let uu____1967 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____1968 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1967 uu____1968 in
               failwith uu____1966) in
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
    | uu____1989 ->
        let uu____1990 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____1990)
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
        (let uu____2133 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2133
         then
           let uu____2134 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2134
         else ());
        (let uu____2136 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2172  ->
                   fun b  ->
                     match uu____2172 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2215 =
                           let x = unmangle (Prims.fst b) in
                           let uu____2224 = gen_term_var env1 x in
                           match uu____2224 with
                           | (xxsym,xx,env') ->
                               let uu____2238 =
                                 let uu____2241 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2241 env1 xx in
                               (match uu____2238 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2215 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2136 with
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
          let uu____2329 = encode_term t env in
          match uu____2329 with
          | (t1,decls) ->
              let uu____2336 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2336, decls)
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
          let uu____2344 = encode_term t env in
          match uu____2344 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2353 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2353, decls)
               | Some f ->
                   let uu____2355 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2355, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2362 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2362
       then
         let uu____2363 = FStar_Syntax_Print.tag_of_term t in
         let uu____2364 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2365 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2363 uu____2364
           uu____2365
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2370 =
             let uu____2371 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2372 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2373 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2374 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2371
               uu____2372 uu____2373 uu____2374 in
           failwith uu____2370
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2378 =
             let uu____2379 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2379 in
           failwith uu____2378
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2384) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2414) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2423 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2423, [])
       | FStar_Syntax_Syntax.Tm_type uu____2429 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2432) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2438 = encode_const c in (uu____2438, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let uu____2452 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2452 with
            | (binders1,res) ->
                let uu____2459 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2459
                then
                  let uu____2462 = encode_binders None binders1 env in
                  (match uu____2462 with
                   | (vars,guards,env',decls,uu____2477) ->
                       let fsym =
                         let uu____2487 = varops.fresh "f" in
                         (uu____2487, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2490 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___144_2494 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___144_2494.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___144_2494.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___144_2494.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___144_2494.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___144_2494.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___144_2494.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___144_2494.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___144_2494.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___144_2494.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___144_2494.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___144_2494.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___144_2494.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___144_2494.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___144_2494.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___144_2494.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___144_2494.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___144_2494.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___144_2494.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___144_2494.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___144_2494.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___144_2494.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___144_2494.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___144_2494.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2490 with
                        | (pre_opt,res_t) ->
                            let uu____2501 =
                              encode_term_pred None res_t env' app in
                            (match uu____2501 with
                             | (res_pred,decls') ->
                                 let uu____2508 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2515 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2515, [])
                                   | Some pre ->
                                       let uu____2518 =
                                         encode_formula pre env' in
                                       (match uu____2518 with
                                        | (guard,decls0) ->
                                            let uu____2526 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2526, decls0)) in
                                 (match uu____2508 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2534 =
                                          let uu____2540 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2540) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2534 in
                                      let cvars =
                                        let uu____2550 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2550
                                          (FStar_List.filter
                                             (fun uu____2556  ->
                                                match uu____2556 with
                                                | (x,uu____2560) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2571 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2571 with
                                       | Some (t',sorts,uu____2587) ->
                                           let uu____2597 =
                                             let uu____2598 =
                                               let uu____2602 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               (t', uu____2602) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2598 in
                                           (uu____2597, [])
                                       | None  ->
                                           let tsym =
                                             let uu____2618 =
                                               let uu____2619 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2619 in
                                             varops.mk_unique uu____2618 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2626 =
                                               FStar_Options.log_queries () in
                                             if uu____2626
                                             then
                                               let uu____2628 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2628
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2634 =
                                               let uu____2638 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2638) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2634 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____2646 =
                                               let uu____2650 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2650, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2646 in
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
                                             let uu____2663 =
                                               let uu____2667 =
                                                 let uu____2668 =
                                                   let uu____2674 =
                                                     let uu____2675 =
                                                       let uu____2678 =
                                                         let uu____2679 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2679 in
                                                       (f_has_t, uu____2678) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2675 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2674) in
                                                 mkForall_fuel uu____2668 in
                                               (uu____2667,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2663 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____2692 =
                                               let uu____2696 =
                                                 let uu____2697 =
                                                   let uu____2703 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2703) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2697 in
                                               (uu____2696, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2692 in
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
                     let uu____2734 =
                       let uu____2738 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____2738, (Some "Typing for non-total arrows"),
                         a_name) in
                     FStar_SMTEncoding_Term.Assume uu____2734 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____2747 =
                       let uu____2751 =
                         let uu____2752 =
                           let uu____2758 =
                             let uu____2759 =
                               let uu____2762 =
                                 let uu____2763 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2763 in
                               (f_has_t, uu____2762) in
                             FStar_SMTEncoding_Util.mkImp uu____2759 in
                           ([[f_has_t]], [fsym], uu____2758) in
                         mkForall_fuel uu____2752 in
                       (uu____2751, (Some a_name), a_name) in
                     FStar_SMTEncoding_Term.Assume uu____2747 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2777 ->
           let uu____2782 =
             let uu____2785 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2785 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2790;
                 FStar_Syntax_Syntax.pos = uu____2791;
                 FStar_Syntax_Syntax.vars = uu____2792;_} ->
                 let uu____2799 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2799 with
                  | (b,f1) ->
                      let uu____2813 =
                        let uu____2814 = FStar_List.hd b in
                        Prims.fst uu____2814 in
                      (uu____2813, f1))
             | uu____2819 -> failwith "impossible" in
           (match uu____2782 with
            | (x,f) ->
                let uu____2826 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____2826 with
                 | (base_t,decls) ->
                     let uu____2833 = gen_term_var env x in
                     (match uu____2833 with
                      | (x1,xtm,env') ->
                          let uu____2842 = encode_formula f env' in
                          (match uu____2842 with
                           | (refinement,decls') ->
                               let uu____2849 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____2849 with
                                | (fsym,fterm) ->
                                    let encoding =
                                      let uu____2857 =
                                        let uu____2860 =
                                          FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                            (Some fterm) xtm base_t in
                                        (uu____2860, refinement) in
                                      FStar_SMTEncoding_Util.mkAnd uu____2857 in
                                    let cvars =
                                      let uu____2865 =
                                        FStar_SMTEncoding_Term.free_variables
                                          encoding in
                                      FStar_All.pipe_right uu____2865
                                        (FStar_List.filter
                                           (fun uu____2871  ->
                                              match uu____2871 with
                                              | (y,uu____2875) ->
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
                                    let uu____2894 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2894 with
                                     | Some (t1,uu____2909,uu____2910) ->
                                         let uu____2920 =
                                           let uu____2921 =
                                             let uu____2925 =
                                               FStar_All.pipe_right cvars
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             (t1, uu____2925) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2921 in
                                         (uu____2920, [])
                                     | None  ->
                                         let tsym =
                                           let uu____2941 =
                                             let uu____2942 =
                                               FStar_Util.digest_of_string
                                                 tkey_hash in
                                             Prims.strcat "Tm_refine_"
                                               uu____2942 in
                                           varops.mk_unique uu____2941 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____2951 =
                                             let uu____2955 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars in
                                             (tsym, uu____2955) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2951 in
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
                                           let uu____2965 =
                                             let uu____2969 =
                                               let uu____2970 =
                                                 let uu____2976 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars,
                                                   uu____2976) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____2970 in
                                             (uu____2969,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____2965 in
                                         let t_kinding =
                                           let uu____2986 =
                                             let uu____2990 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars,
                                                   t_has_kind) in
                                             (uu____2990,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____2986 in
                                         let t_interp =
                                           let uu____3000 =
                                             let uu____3004 =
                                               let uu____3005 =
                                                 let uu____3011 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars), uu____3011) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3005 in
                                             let uu____3023 =
                                               let uu____3025 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3025 in
                                             (uu____3004, uu____3023,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3000 in
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
             let uu____3053 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3053 in
           let uu____3057 = encode_term_pred None k env ttm in
           (match uu____3057 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3065 =
                    let uu____3069 =
                      let uu____3070 =
                        let uu____3071 =
                          let uu____3072 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3072 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3071 in
                      varops.mk_unique uu____3070 in
                    (t_has_k, (Some "Uvar typing"), uu____3069) in
                  FStar_SMTEncoding_Term.Assume uu____3065 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3078 ->
           let uu____3088 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3088 with
            | (head1,args_e) ->
                let uu____3116 =
                  let uu____3124 =
                    let uu____3125 = FStar_Syntax_Subst.compress head1 in
                    uu____3125.FStar_Syntax_Syntax.n in
                  (uu____3124, args_e) in
                (match uu____3116 with
                 | (uu____3135,uu____3136) when head_redex env head1 ->
                     let uu____3147 = whnf env t in
                     encode_term uu____3147 env
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
                     let uu____3221 = encode_term v1 env in
                     (match uu____3221 with
                      | (v11,decls1) ->
                          let uu____3228 = encode_term v2 env in
                          (match uu____3228 with
                           | (v21,decls2) ->
                               let uu____3235 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3235,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3237) ->
                     let e0 =
                       let uu____3251 =
                         let uu____3254 =
                           let uu____3255 =
                             let uu____3265 =
                               let uu____3271 = FStar_List.hd args_e in
                               [uu____3271] in
                             (head1, uu____3265) in
                           FStar_Syntax_Syntax.Tm_app uu____3255 in
                         FStar_Syntax_Syntax.mk uu____3254 in
                       uu____3251 None head1.FStar_Syntax_Syntax.pos in
                     ((let uu____3304 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3304
                       then
                         let uu____3305 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Trying to normalize %s\n"
                           uu____3305
                       else ());
                      (let e01 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Reify;
                           FStar_TypeChecker_Normalize.Eager_unfolding;
                           FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                           env.tcenv e0 in
                       (let uu____3309 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify") in
                        if uu____3309
                        then
                          let uu____3310 =
                            FStar_Syntax_Print.term_to_string e01 in
                          FStar_Util.print1 "Result of normalization %s\n"
                            uu____3310
                        else ());
                       (let e02 =
                          let uu____3313 =
                            let uu____3314 =
                              let uu____3315 =
                                FStar_Syntax_Subst.compress e01 in
                              uu____3315.FStar_Syntax_Syntax.n in
                            match uu____3314 with
                            | FStar_Syntax_Syntax.Tm_app uu____3318 -> false
                            | uu____3328 -> true in
                          if uu____3313
                          then e01
                          else
                            (let uu____3330 =
                               FStar_Syntax_Util.head_and_args e01 in
                             match uu____3330 with
                             | (head2,args) ->
                                 let uu____3356 =
                                   let uu____3357 =
                                     let uu____3358 =
                                       FStar_Syntax_Subst.compress head2 in
                                     uu____3358.FStar_Syntax_Syntax.n in
                                   match uu____3357 with
                                   | FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_reify ) -> true
                                   | uu____3361 -> false in
                                 if uu____3356
                                 then
                                   (match args with
                                    | x::[] -> Prims.fst x
                                    | uu____3377 ->
                                        failwith
                                          "Impossible : Reify applied to multiple arguments after normalization.")
                                 else e01) in
                        let e =
                          match args_e with
                          | uu____3385::[] -> e02
                          | uu____3398 ->
                              let uu____3404 =
                                let uu____3407 =
                                  let uu____3408 =
                                    let uu____3418 = FStar_List.tl args_e in
                                    (e02, uu____3418) in
                                  FStar_Syntax_Syntax.Tm_app uu____3408 in
                                FStar_Syntax_Syntax.mk uu____3407 in
                              uu____3404 None t0.FStar_Syntax_Syntax.pos in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3441),(arg,uu____3443)::[]) -> encode_term arg env
                 | uu____3461 ->
                     let uu____3469 = encode_args args_e env in
                     (match uu____3469 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3502 = encode_term head1 env in
                            match uu____3502 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3541 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3541 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3583  ->
                                                 fun uu____3584  ->
                                                   match (uu____3583,
                                                           uu____3584)
                                                   with
                                                   | ((bv,uu____3598),
                                                      (a,uu____3600)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3614 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3614
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3619 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3619 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3629 =
                                                   let uu____3633 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
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
                                                   (uu____3633,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3638) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3629 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3658 = lookup_free_var_sym env fv in
                            match uu____3658 with
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
                                let uu____3696 =
                                  let uu____3697 =
                                    let uu____3700 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3700 Prims.fst in
                                  FStar_All.pipe_right uu____3697 Prims.snd in
                                Some uu____3696
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3719,(FStar_Util.Inl t1,uu____3721),uu____3722)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3760,(FStar_Util.Inr c,uu____3762),uu____3763)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3801 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3821 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3821 in
                               let uu____3822 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3822 with
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
                                     | uu____3847 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3892 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3892 with
            | (bs1,body1,opening) ->
                let fallback uu____3907 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3912 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3912, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3923 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3923
                  | FStar_Util.Inr (eff,uu____3925) ->
                      let uu____3931 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3931 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body = reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____3976 =
                            FStar_Syntax_Syntax.get_comp_of_lcomp lc in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___145_3977 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___145_3977.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___145_3977.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___145_3977.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___145_3977.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___145_3977.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___145_3977.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___145_3977.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___145_3977.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___145_3977.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___145_3977.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___145_3977.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___145_3977.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___145_3977.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___145_3977.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___145_3977.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___145_3977.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___145_3977.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___145_3977.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___145_3977.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___145_3977.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___145_3977.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___145_3977.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___145_3977.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____3976 FStar_Syntax_Syntax.U_unknown in
                        let uu____3978 =
                          let uu____3979 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____3979 in
                        FStar_Util.Inl uu____3978
                    | FStar_Util.Inr (eff_name,uu____3986) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4017 =
                        let uu____4018 =
                          FStar_Syntax_Syntax.get_comp_of_lcomp lc1 in
                        FStar_Syntax_Subst.subst_comp opening uu____4018 in
                      FStar_All.pipe_right uu____4017
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4030 =
                        let uu____4031 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4031 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4039 =
                          let uu____4040 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4040 in
                        FStar_All.pipe_right uu____4039
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4044 =
                             let uu____4045 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4045 in
                           FStar_All.pipe_right uu____4044
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4056 =
                         let uu____4057 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4057 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4056);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4072 =
                       (is_impure lc1) &&
                         (let uu____4073 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4073) in
                     if uu____4072
                     then fallback ()
                     else
                       (let uu____4077 = encode_binders None bs1 env in
                        match uu____4077 with
                        | (vars,guards,envbody,decls,uu____4092) ->
                            let uu____4099 =
                              let uu____4107 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4107
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4099 with
                             | (lc2,body2) ->
                                 let uu____4132 = encode_term body2 envbody in
                                 (match uu____4132 with
                                  | (body3,decls') ->
                                      let key_body =
                                        let uu____4140 =
                                          let uu____4146 =
                                            let uu____4147 =
                                              let uu____4150 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____4150, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____4147 in
                                          ([], vars, uu____4146) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4140 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____4161 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____4161 with
                                       | Some (t1,uu____4176,uu____4177) ->
                                           let uu____4187 =
                                             let uu____4188 =
                                               let uu____4192 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (t1, uu____4192) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4188 in
                                           (uu____4187, [])
                                       | None  ->
                                           let uu____4203 =
                                             is_eta env vars body3 in
                                           (match uu____4203 with
                                            | Some t1 -> (t1, [])
                                            | None  ->
                                                let cvar_sorts =
                                                  FStar_List.map Prims.snd
                                                    cvars in
                                                let fsym =
                                                  let uu____4214 =
                                                    let uu____4215 =
                                                      FStar_Util.digest_of_string
                                                        tkey_hash in
                                                    Prims.strcat "Tm_abs_"
                                                      uu____4215 in
                                                  varops.mk_unique uu____4214 in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      None) in
                                                let f =
                                                  let uu____4220 =
                                                    let uu____4224 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars in
                                                    (fsym, uu____4224) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4220 in
                                                let app = mk_Apply f vars in
                                                let typing_f =
                                                  let uu____4232 =
                                                    codomain_eff lc2 in
                                                  match uu____4232 with
                                                  | None  -> []
                                                  | Some c ->
                                                      let tfun =
                                                        FStar_Syntax_Util.arrow
                                                          bs1 c in
                                                      let uu____4239 =
                                                        encode_term_pred None
                                                          tfun env f in
                                                      (match uu____4239 with
                                                       | (f_has_t,decls'') ->
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym in
                                                           let uu____4246 =
                                                             let uu____4248 =
                                                               let uu____4249
                                                                 =
                                                                 let uu____4253
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkForall
                                                                    ([[f]],
                                                                    cvars,
                                                                    f_has_t) in
                                                                 (uu____4253,
                                                                   (Some
                                                                    a_name),
                                                                   a_name) in
                                                               FStar_SMTEncoding_Term.Assume
                                                                 uu____4249 in
                                                             [uu____4248] in
                                                           FStar_List.append
                                                             decls''
                                                             uu____4246) in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____4261 =
                                                    let uu____4265 =
                                                      let uu____4266 =
                                                        let uu____4272 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars),
                                                          uu____4272) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____4266 in
                                                    (uu____4265,
                                                      (Some a_name), a_name) in
                                                  FStar_SMTEncoding_Term.Assume
                                                    uu____4261 in
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
           ((uu____4290,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4291;
                          FStar_Syntax_Syntax.lbunivs = uu____4292;
                          FStar_Syntax_Syntax.lbtyp = uu____4293;
                          FStar_Syntax_Syntax.lbeff = uu____4294;
                          FStar_Syntax_Syntax.lbdef = uu____4295;_}::uu____4296),uu____4297)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4315;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4317;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4333 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4346 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4346, [decl_e])))
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
              let uu____4388 = encode_term e1 env in
              match uu____4388 with
              | (ee1,decls1) ->
                  let uu____4395 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4395 with
                   | (xs,e21) ->
                       let uu____4409 = FStar_List.hd xs in
                       (match uu____4409 with
                        | (x1,uu____4417) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4419 = encode_body e21 env' in
                            (match uu____4419 with
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
            let uu____4441 =
              let uu____4445 =
                let uu____4446 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4446 in
              gen_term_var env uu____4445 in
            match uu____4441 with
            | (scrsym,scr',env1) ->
                let uu____4460 = encode_term e env1 in
                (match uu____4460 with
                 | (scr,decls) ->
                     let uu____4467 =
                       let encode_branch b uu____4483 =
                         match uu____4483 with
                         | (else_case,decls1) ->
                             let uu____4494 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4494 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4524  ->
                                       fun uu____4525  ->
                                         match (uu____4524, uu____4525) with
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
                                                       fun uu____4562  ->
                                                         match uu____4562
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4567 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4582 =
                                                     encode_term w1 env2 in
                                                   (match uu____4582 with
                                                    | (w2,decls21) ->
                                                        let uu____4590 =
                                                          let uu____4591 =
                                                            let uu____4594 =
                                                              let uu____4595
                                                                =
                                                                let uu____4598
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4598) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4595 in
                                                            (guard,
                                                              uu____4594) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4591 in
                                                        (uu____4590, decls21)) in
                                             (match uu____4567 with
                                              | (guard1,decls21) ->
                                                  let uu____4606 =
                                                    encode_br br env2 in
                                                  (match uu____4606 with
                                                   | (br1,decls3) ->
                                                       let uu____4614 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4614,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4467 with
                      | (match_tm,decls1) ->
                          let uu____4626 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4626, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4657 -> let uu____4658 = encode_one_pat env pat in [uu____4658]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4670 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4670
       then
         let uu____4671 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4671
       else ());
      (let uu____4673 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4673 with
       | (vars,pat_term) ->
           let uu____4683 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4706  ->
                     fun v1  ->
                       match uu____4706 with
                       | (env1,vars1) ->
                           let uu____4734 = gen_term_var env1 v1 in
                           (match uu____4734 with
                            | (xx,uu____4746,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4683 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4793 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4801 =
                        let uu____4804 = encode_const c in
                        (scrutinee, uu____4804) in
                      FStar_SMTEncoding_Util.mkEq uu____4801
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4823 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4823 with
                        | (uu____4827,uu____4828::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4830 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4851  ->
                                  match uu____4851 with
                                  | (arg,uu____4857) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4867 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4867)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4886 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4901 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4916 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4938  ->
                                  match uu____4938 with
                                  | (arg,uu____4947) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4957 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____4957)) in
                      FStar_All.pipe_right uu____4916 FStar_List.flatten in
                let pat_term1 uu____4973 = encode_term pat_term env1 in
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
      let uu____4980 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____4995  ->
                fun uu____4996  ->
                  match (uu____4995, uu____4996) with
                  | ((tms,decls),(t,uu____5016)) ->
                      let uu____5027 = encode_term t env in
                      (match uu____5027 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____4980 with | (l1,decls) -> ((FStar_List.rev l1), decls)
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
            let uu____5065 = FStar_Syntax_Util.list_elements e in
            match uu____5065 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 []) in
          let one_pat p =
            let uu____5083 =
              let uu____5093 = FStar_Syntax_Util.unmeta p in
              FStar_All.pipe_right uu____5093 FStar_Syntax_Util.head_and_args in
            match uu____5083 with
            | (head1,args) ->
                let uu____5124 =
                  let uu____5132 =
                    let uu____5133 = FStar_Syntax_Util.un_uinst head1 in
                    uu____5133.FStar_Syntax_Syntax.n in
                  (uu____5132, args) in
                (match uu____5124 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5147,uu____5148)::(e,uu____5150)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5181)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5202 -> failwith "Unexpected pattern term") in
          let lemma_pats p =
            let elts = list_elements1 p in
            let smt_pat_or t1 =
              let uu____5235 =
                let uu____5245 = FStar_Syntax_Util.unmeta t1 in
                FStar_All.pipe_right uu____5245
                  FStar_Syntax_Util.head_and_args in
              match uu____5235 with
              | (head1,args) ->
                  let uu____5274 =
                    let uu____5282 =
                      let uu____5283 = FStar_Syntax_Util.un_uinst head1 in
                      uu____5283.FStar_Syntax_Syntax.n in
                    (uu____5282, args) in
                  (match uu____5274 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5296)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5316 -> None) in
            match elts with
            | t1::[] ->
                let uu____5334 = smt_pat_or t1 in
                (match uu____5334 with
                 | Some e ->
                     let uu____5350 = list_elements1 e in
                     FStar_All.pipe_right uu____5350
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5367 = list_elements1 branch1 in
                             FStar_All.pipe_right uu____5367
                               (FStar_List.map one_pat)))
                 | uu____5381 ->
                     let uu____5385 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat) in
                     [uu____5385])
            | uu____5416 ->
                let uu____5418 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat) in
                [uu____5418] in
          let uu____5449 =
            let uu____5465 =
              let uu____5466 = FStar_Syntax_Subst.compress t in
              uu____5466.FStar_Syntax_Syntax.n in
            match uu____5465 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5496 = FStar_Syntax_Subst.open_comp binders c in
                (match uu____5496 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5531;
                            FStar_Syntax_Syntax.effect_name = uu____5532;
                            FStar_Syntax_Syntax.result_typ = uu____5533;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5535)::(post,uu____5537)::(pats,uu____5539)::[];
                            FStar_Syntax_Syntax.flags = uu____5540;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats in
                          let uu____5574 = lemma_pats pats' in
                          (binders1, pre, post, uu____5574)
                      | uu____5593 -> failwith "impos"))
            | uu____5609 -> failwith "Impos" in
          match uu____5449 with
          | (binders,pre,post,patterns) ->
              let uu____5653 = encode_binders None binders env in
              (match uu____5653 with
               | (vars,guards,env1,decls,uu____5668) ->
                   let uu____5675 =
                     let uu____5682 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5713 =
                                 let uu____5718 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5734  ->
                                           match uu____5734 with
                                           | (t1,uu____5741) ->
                                               encode_term t1
                                                 (let uu___146_5744 = env1 in
                                                  {
                                                    bindings =
                                                      (uu___146_5744.bindings);
                                                    depth =
                                                      (uu___146_5744.depth);
                                                    tcenv =
                                                      (uu___146_5744.tcenv);
                                                    warn =
                                                      (uu___146_5744.warn);
                                                    cache =
                                                      (uu___146_5744.cache);
                                                    nolabels =
                                                      (uu___146_5744.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___146_5744.encode_non_total_function_typ)
                                                  }))) in
                                 FStar_All.pipe_right uu____5718
                                   FStar_List.unzip in
                               match uu____5713 with
                               | (pats,decls1) -> (pats, decls1))) in
                     FStar_All.pipe_right uu____5682 FStar_List.unzip in
                   (match uu____5675 with
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
                                           let uu____5808 =
                                             let uu____5809 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5809 e in
                                           uu____5808 :: p))
                               | uu____5810 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5839 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e in
                                                 uu____5839 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5847 =
                                           let uu____5848 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort) in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5848 tl1 in
                                         aux uu____5847 vars2
                                     | uu____5849 -> pats in
                                   let uu____5853 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort) in
                                   aux uu____5853 vars) in
                        let env2 =
                          let uu___147_5855 = env1 in
                          {
                            bindings = (uu___147_5855.bindings);
                            depth = (uu___147_5855.depth);
                            tcenv = (uu___147_5855.tcenv);
                            warn = (uu___147_5855.warn);
                            cache = (uu___147_5855.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___147_5855.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___147_5855.encode_non_total_function_typ)
                          } in
                        let uu____5856 =
                          let uu____5859 = FStar_Syntax_Util.unmeta pre in
                          encode_formula uu____5859 env2 in
                        (match uu____5856 with
                         | (pre1,decls'') ->
                             let uu____5864 =
                               let uu____5867 = FStar_Syntax_Util.unmeta post in
                               encode_formula uu____5867 env2 in
                             (match uu____5864 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls''')) in
                                  let uu____5874 =
                                    let uu____5875 =
                                      let uu____5881 =
                                        let uu____5882 =
                                          let uu____5885 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards) in
                                          (uu____5885, post1) in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5882 in
                                      (pats1, vars, uu____5881) in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5875 in
                                  (uu____5874, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5898 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5898
        then
          let uu____5899 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5900 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5899 uu____5900
        else () in
      let enc f r l =
        let uu____5927 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5940 = encode_term (Prims.fst x) env in
                 match uu____5940 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5927 with
        | (decls,args) ->
            let uu____5957 =
              let uu___148_5958 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___148_5958.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___148_5958.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5957, decls) in
      let const_op f r uu____5977 = let uu____5980 = f r in (uu____5980, []) in
      let un_op f l =
        let uu____5996 = FStar_List.hd l in FStar_All.pipe_left f uu____5996 in
      let bin_op f uu___120_6009 =
        match uu___120_6009 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6017 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6044 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6053  ->
                 match uu____6053 with
                 | (t,uu____6061) ->
                     let uu____6062 = encode_formula t env in
                     (match uu____6062 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6044 with
        | (decls,phis) ->
            let uu____6079 =
              let uu___149_6080 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___149_6080.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___149_6080.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6079, decls) in
      let eq_op r uu___121_6096 =
        match uu___121_6096 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6156 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6156 r [e1; e2]
        | l ->
            let uu____6176 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6176 r l in
      let mk_imp1 r uu___122_6195 =
        match uu___122_6195 with
        | (lhs,uu____6199)::(rhs,uu____6201)::[] ->
            let uu____6222 = encode_formula rhs env in
            (match uu____6222 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6231) ->
                      (l1, decls1)
                  | uu____6234 ->
                      let uu____6235 = encode_formula lhs env in
                      (match uu____6235 with
                       | (l2,decls2) ->
                           let uu____6242 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6242, (FStar_List.append decls1 decls2)))))
        | uu____6244 -> failwith "impossible" in
      let mk_ite r uu___123_6259 =
        match uu___123_6259 with
        | (guard,uu____6263)::(_then,uu____6265)::(_else,uu____6267)::[] ->
            let uu____6296 = encode_formula guard env in
            (match uu____6296 with
             | (g,decls1) ->
                 let uu____6303 = encode_formula _then env in
                 (match uu____6303 with
                  | (t,decls2) ->
                      let uu____6310 = encode_formula _else env in
                      (match uu____6310 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6319 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6338 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6338 in
      let connectives =
        let uu____6350 =
          let uu____6359 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6359) in
        let uu____6372 =
          let uu____6382 =
            let uu____6391 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6391) in
          let uu____6404 =
            let uu____6414 =
              let uu____6424 =
                let uu____6433 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6433) in
              let uu____6446 =
                let uu____6456 =
                  let uu____6466 =
                    let uu____6475 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6475) in
                  [uu____6466;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6456 in
              uu____6424 :: uu____6446 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6414 in
          uu____6382 :: uu____6404 in
        uu____6350 :: uu____6372 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6637 = encode_formula phi' env in
            (match uu____6637 with
             | (phi2,decls) ->
                 let uu____6644 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6644, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6645 ->
            let uu____6650 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6650 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6679 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6679 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6687;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6689;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6705 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6705 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6737::(x,uu____6739)::(t,uu____6741)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6775 = encode_term x env in
                 (match uu____6775 with
                  | (x1,decls) ->
                      let uu____6782 = encode_term t env in
                      (match uu____6782 with
                       | (t1,decls') ->
                           let uu____6789 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6789, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6793)::(msg,uu____6795)::(phi2,uu____6797)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6831 =
                   let uu____6834 =
                     let uu____6835 = FStar_Syntax_Subst.compress r in
                     uu____6835.FStar_Syntax_Syntax.n in
                   let uu____6838 =
                     let uu____6839 = FStar_Syntax_Subst.compress msg in
                     uu____6839.FStar_Syntax_Syntax.n in
                   (uu____6834, uu____6838) in
                 (match uu____6831 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6846))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6862 -> fallback phi2)
             | uu____6865 when head_redex env head2 ->
                 let uu____6873 = whnf env phi1 in
                 encode_formula uu____6873 env
             | uu____6874 ->
                 let uu____6882 = encode_term phi1 env in
                 (match uu____6882 with
                  | (tt,decls) ->
                      let uu____6889 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___150_6890 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___150_6890.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___150_6890.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6889, decls)))
        | uu____6893 ->
            let uu____6894 = encode_term phi1 env in
            (match uu____6894 with
             | (tt,decls) ->
                 let uu____6901 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___151_6902 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___151_6902.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___151_6902.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6901, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6929 = encode_binders None bs env1 in
        match uu____6929 with
        | (vars,guards,env2,decls,uu____6951) ->
            let uu____6958 =
              let uu____6965 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____6988 =
                          let uu____6993 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7007  ->
                                    match uu____7007 with
                                    | (t,uu____7013) ->
                                        encode_term t
                                          (let uu___152_7014 = env2 in
                                           {
                                             bindings =
                                               (uu___152_7014.bindings);
                                             depth = (uu___152_7014.depth);
                                             tcenv = (uu___152_7014.tcenv);
                                             warn = (uu___152_7014.warn);
                                             cache = (uu___152_7014.cache);
                                             nolabels =
                                               (uu___152_7014.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___152_7014.encode_non_total_function_typ)
                                           }))) in
                          FStar_All.pipe_right uu____6993 FStar_List.unzip in
                        match uu____6988 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____6965 FStar_List.unzip in
            (match uu____6958 with
             | (pats,decls') ->
                 let uu____7066 = encode_formula body env2 in
                 (match uu____7066 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7085;
                             FStar_SMTEncoding_Term.rng = uu____7086;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7094 -> guards in
                      let uu____7097 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7097, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7131  ->
                   match uu____7131 with
                   | (x,uu____7135) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7141 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7147 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7147) uu____7141 tl1 in
             let uu____7149 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7161  ->
                       match uu____7161 with
                       | (b,uu____7165) ->
                           let uu____7166 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7166)) in
             (match uu____7149 with
              | None  -> ()
              | Some (x,uu____7170) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7180 =
                    let uu____7181 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7181 in
                  FStar_Errors.warn pos uu____7180) in
       let uu____7182 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7182 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7188 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7224  ->
                     match uu____7224 with
                     | (l,uu____7234) -> FStar_Ident.lid_equals op l)) in
           (match uu____7188 with
            | None  -> fallback phi1
            | Some (uu____7257,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7286 = encode_q_body env vars pats body in
             match uu____7286 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7312 =
                     let uu____7318 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7318) in
                   FStar_SMTEncoding_Term.mkForall uu____7312
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7330 = encode_q_body env vars pats body in
             match uu____7330 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7355 =
                   let uu____7356 =
                     let uu____7362 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7362) in
                   FStar_SMTEncoding_Term.mkExists uu____7356
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7355, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7411 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7411 with
  | (asym,a) ->
      let uu____7416 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7416 with
       | (xsym,x) ->
           let uu____7421 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7421 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7451 =
                      let uu____7457 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7457, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7451 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7472 =
                      let uu____7476 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7476) in
                    FStar_SMTEncoding_Util.mkApp uu____7472 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7484 =
                    let uu____7486 =
                      let uu____7488 =
                        let uu____7490 =
                          let uu____7491 =
                            let uu____7495 =
                              let uu____7496 =
                                let uu____7502 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7502) in
                              FStar_SMTEncoding_Util.mkForall uu____7496 in
                            (uu____7495, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Term.Assume uu____7491 in
                        let uu____7511 =
                          let uu____7513 =
                            let uu____7514 =
                              let uu____7518 =
                                let uu____7519 =
                                  let uu____7525 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7525) in
                                FStar_SMTEncoding_Util.mkForall uu____7519 in
                              (uu____7518,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Term.Assume uu____7514 in
                          [uu____7513] in
                        uu____7490 :: uu____7511 in
                      xtok_decl :: uu____7488 in
                    xname_decl :: uu____7486 in
                  (xtok1, uu____7484) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7574 =
                    let uu____7582 =
                      let uu____7588 =
                        let uu____7589 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7589 in
                      quant axy uu____7588 in
                    (FStar_Syntax_Const.op_Eq, uu____7582) in
                  let uu____7595 =
                    let uu____7604 =
                      let uu____7612 =
                        let uu____7618 =
                          let uu____7619 =
                            let uu____7620 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7620 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7619 in
                        quant axy uu____7618 in
                      (FStar_Syntax_Const.op_notEq, uu____7612) in
                    let uu____7626 =
                      let uu____7635 =
                        let uu____7643 =
                          let uu____7649 =
                            let uu____7650 =
                              let uu____7651 =
                                let uu____7654 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7655 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7654, uu____7655) in
                              FStar_SMTEncoding_Util.mkLT uu____7651 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7650 in
                          quant xy uu____7649 in
                        (FStar_Syntax_Const.op_LT, uu____7643) in
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
                                FStar_SMTEncoding_Util.mkLTE uu____7686 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7685 in
                            quant xy uu____7684 in
                          (FStar_Syntax_Const.op_LTE, uu____7678) in
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
                                  FStar_SMTEncoding_Util.mkGT uu____7721 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7720 in
                              quant xy uu____7719 in
                            (FStar_Syntax_Const.op_GT, uu____7713) in
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
                                    FStar_SMTEncoding_Util.mkGTE uu____7756 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7755 in
                                quant xy uu____7754 in
                              (FStar_Syntax_Const.op_GTE, uu____7748) in
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
                                      FStar_SMTEncoding_Util.mkSub uu____7791 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7790 in
                                  quant xy uu____7789 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7783) in
                              let uu____7801 =
                                let uu____7810 =
                                  let uu____7818 =
                                    let uu____7824 =
                                      let uu____7825 =
                                        let uu____7826 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7826 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7825 in
                                    quant qx uu____7824 in
                                  (FStar_Syntax_Const.op_Minus, uu____7818) in
                                let uu____7832 =
                                  let uu____7841 =
                                    let uu____7849 =
                                      let uu____7855 =
                                        let uu____7856 =
                                          let uu____7857 =
                                            let uu____7860 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7861 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7860, uu____7861) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7857 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7856 in
                                      quant xy uu____7855 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7849) in
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
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7892 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7891 in
                                        quant xy uu____7890 in
                                      (FStar_Syntax_Const.op_Multiply,
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
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7927 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7926 in
                                          quant xy uu____7925 in
                                        (FStar_Syntax_Const.op_Division,
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
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____7962 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____7961 in
                                            quant xy uu____7960 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____7954) in
                                        let uu____7972 =
                                          let uu____7981 =
                                            let uu____7989 =
                                              let uu____7995 =
                                                let uu____7996 =
                                                  let uu____7997 =
                                                    let uu____8000 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8001 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8000, uu____8001) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____7997 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____7996 in
                                              quant xy uu____7995 in
                                            (FStar_Syntax_Const.op_And,
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
                                                      (uu____8035,
                                                        uu____8036) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8032 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8031 in
                                                quant xy uu____8030 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8024) in
                                            let uu____8042 =
                                              let uu____8051 =
                                                let uu____8059 =
                                                  let uu____8065 =
                                                    let uu____8066 =
                                                      let uu____8067 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8067 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8066 in
                                                  quant qx uu____8065 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8059) in
                                              [uu____8051] in
                                            uu____8016 :: uu____8042 in
                                          uu____7981 :: uu____8007 in
                                        uu____7946 :: uu____7972 in
                                      uu____7911 :: uu____7937 in
                                    uu____7876 :: uu____7902 in
                                  uu____7841 :: uu____7867 in
                                uu____7810 :: uu____7832 in
                              uu____7775 :: uu____7801 in
                            uu____7740 :: uu____7766 in
                          uu____7705 :: uu____7731 in
                        uu____7670 :: uu____7696 in
                      uu____7635 :: uu____7661 in
                    uu____7604 :: uu____7626 in
                  uu____7574 :: uu____7595 in
                let mk1 l v1 =
                  let uu____8195 =
                    let uu____8200 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8232  ->
                              match uu____8232 with
                              | (l',uu____8241) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8200
                      (FStar_Option.map
                         (fun uu____8274  ->
                            match uu____8274 with | (uu____8285,b) -> b v1)) in
                  FStar_All.pipe_right uu____8195 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8326  ->
                          match uu____8326 with
                          | (l',uu____8335) -> FStar_Ident.lid_equals l l')) in
                { mk = mk1; is }))
let pretype_axiom:
  FStar_SMTEncoding_Term.term ->
    (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.decl
  =
  fun tapp  ->
    fun vars  ->
      let uu____8358 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      match uu____8358 with
      | (xxsym,xx) ->
          let uu____8363 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
          (match uu____8363 with
           | (ffsym,ff) ->
               let xx_has_type =
                 FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
               let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
               let uu____8370 =
                 let uu____8374 =
                   let uu____8375 =
                     let uu____8381 =
                       let uu____8382 =
                         let uu____8385 =
                           let uu____8386 =
                             let uu____8389 =
                               FStar_SMTEncoding_Util.mkApp ("PreType", [xx]) in
                             (tapp, uu____8389) in
                           FStar_SMTEncoding_Util.mkEq uu____8386 in
                         (xx_has_type, uu____8385) in
                       FStar_SMTEncoding_Util.mkImp uu____8382 in
                     ([[xx_has_type]],
                       ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                       (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                       uu____8381) in
                   FStar_SMTEncoding_Util.mkForall uu____8375 in
                 let uu____8402 =
                   let uu____8403 =
                     let uu____8404 = FStar_Util.digest_of_string tapp_hash in
                     Prims.strcat "pretyping_" uu____8404 in
                   varops.mk_unique uu____8403 in
                 (uu____8374, (Some "pretyping"), uu____8402) in
               FStar_SMTEncoding_Term.Assume uu____8370)
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
    let uu____8434 =
      let uu____8435 =
        let uu____8439 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8439, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Term.Assume uu____8435 in
    let uu____8441 =
      let uu____8443 =
        let uu____8444 =
          let uu____8448 =
            let uu____8449 =
              let uu____8455 =
                let uu____8456 =
                  let uu____8459 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8459) in
                FStar_SMTEncoding_Util.mkImp uu____8456 in
              ([[typing_pred]], [xx], uu____8455) in
            mkForall_fuel uu____8449 in
          (uu____8448, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8444 in
      [uu____8443] in
    uu____8434 :: uu____8441 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8487 =
      let uu____8488 =
        let uu____8492 =
          let uu____8493 =
            let uu____8499 =
              let uu____8502 =
                let uu____8504 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8504] in
              [uu____8502] in
            let uu____8507 =
              let uu____8508 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8508 tt in
            (uu____8499, [bb], uu____8507) in
          FStar_SMTEncoding_Util.mkForall uu____8493 in
        (uu____8492, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Term.Assume uu____8488 in
    let uu____8519 =
      let uu____8521 =
        let uu____8522 =
          let uu____8526 =
            let uu____8527 =
              let uu____8533 =
                let uu____8534 =
                  let uu____8537 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8537) in
                FStar_SMTEncoding_Util.mkImp uu____8534 in
              ([[typing_pred]], [xx], uu____8533) in
            mkForall_fuel uu____8527 in
          (uu____8526, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8522 in
      [uu____8521] in
    uu____8487 :: uu____8519 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8571 =
        let uu____8572 =
          let uu____8576 =
            let uu____8578 =
              let uu____8580 =
                let uu____8582 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8583 =
                  let uu____8585 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8585] in
                uu____8582 :: uu____8583 in
              tt :: uu____8580 in
            tt :: uu____8578 in
          ("Prims.Precedes", uu____8576) in
        FStar_SMTEncoding_Util.mkApp uu____8572 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8571 in
    let precedes_y_x =
      let uu____8588 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8588 in
    let uu____8590 =
      let uu____8591 =
        let uu____8595 =
          let uu____8596 =
            let uu____8602 =
              let uu____8605 =
                let uu____8607 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8607] in
              [uu____8605] in
            let uu____8610 =
              let uu____8611 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8611 tt in
            (uu____8602, [bb], uu____8610) in
          FStar_SMTEncoding_Util.mkForall uu____8596 in
        (uu____8595, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Term.Assume uu____8591 in
    let uu____8622 =
      let uu____8624 =
        let uu____8625 =
          let uu____8629 =
            let uu____8630 =
              let uu____8636 =
                let uu____8637 =
                  let uu____8640 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8640) in
                FStar_SMTEncoding_Util.mkImp uu____8637 in
              ([[typing_pred]], [xx], uu____8636) in
            mkForall_fuel uu____8630 in
          (uu____8629, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8625 in
      let uu____8653 =
        let uu____8655 =
          let uu____8656 =
            let uu____8660 =
              let uu____8661 =
                let uu____8667 =
                  let uu____8668 =
                    let uu____8671 =
                      let uu____8672 =
                        let uu____8674 =
                          let uu____8676 =
                            let uu____8678 =
                              let uu____8679 =
                                let uu____8682 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8683 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8682, uu____8683) in
                              FStar_SMTEncoding_Util.mkGT uu____8679 in
                            let uu____8684 =
                              let uu____8686 =
                                let uu____8687 =
                                  let uu____8690 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8691 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8690, uu____8691) in
                                FStar_SMTEncoding_Util.mkGTE uu____8687 in
                              let uu____8692 =
                                let uu____8694 =
                                  let uu____8695 =
                                    let uu____8698 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8699 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8698, uu____8699) in
                                  FStar_SMTEncoding_Util.mkLT uu____8695 in
                                [uu____8694] in
                              uu____8686 :: uu____8692 in
                            uu____8678 :: uu____8684 in
                          typing_pred_y :: uu____8676 in
                        typing_pred :: uu____8674 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8672 in
                    (uu____8671, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8668 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8667) in
              mkForall_fuel uu____8661 in
            (uu____8660, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Term.Assume uu____8656 in
        [uu____8655] in
      uu____8624 :: uu____8653 in
    uu____8590 :: uu____8622 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8729 =
      let uu____8730 =
        let uu____8734 =
          let uu____8735 =
            let uu____8741 =
              let uu____8744 =
                let uu____8746 = FStar_SMTEncoding_Term.boxString b in
                [uu____8746] in
              [uu____8744] in
            let uu____8749 =
              let uu____8750 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8750 tt in
            (uu____8741, [bb], uu____8749) in
          FStar_SMTEncoding_Util.mkForall uu____8735 in
        (uu____8734, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Term.Assume uu____8730 in
    let uu____8761 =
      let uu____8763 =
        let uu____8764 =
          let uu____8768 =
            let uu____8769 =
              let uu____8775 =
                let uu____8776 =
                  let uu____8779 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8779) in
                FStar_SMTEncoding_Util.mkImp uu____8776 in
              ([[typing_pred]], [xx], uu____8775) in
            mkForall_fuel uu____8769 in
          (uu____8768, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8764 in
      [uu____8763] in
    uu____8729 :: uu____8761 in
  let mk_ref1 env reft_name uu____8801 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8812 =
        let uu____8816 =
          let uu____8818 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8818] in
        (reft_name, uu____8816) in
      FStar_SMTEncoding_Util.mkApp uu____8812 in
    let refb =
      let uu____8821 =
        let uu____8825 =
          let uu____8827 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8827] in
        (reft_name, uu____8825) in
      FStar_SMTEncoding_Util.mkApp uu____8821 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8831 =
      let uu____8832 =
        let uu____8836 =
          let uu____8837 =
            let uu____8843 =
              let uu____8844 =
                let uu____8847 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8847) in
              FStar_SMTEncoding_Util.mkImp uu____8844 in
            ([[typing_pred]], [xx; aa], uu____8843) in
          mkForall_fuel uu____8837 in
        (uu____8836, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Term.Assume uu____8832 in
    let uu____8862 =
      let uu____8864 =
        let uu____8865 =
          let uu____8869 =
            let uu____8870 =
              let uu____8876 =
                let uu____8877 =
                  let uu____8880 =
                    FStar_SMTEncoding_Util.mkAnd (typing_pred, typing_pred_b) in
                  let uu____8881 =
                    let uu____8882 =
                      let uu____8885 = FStar_SMTEncoding_Util.mkFreeV aa in
                      let uu____8886 = FStar_SMTEncoding_Util.mkFreeV bb in
                      (uu____8885, uu____8886) in
                    FStar_SMTEncoding_Util.mkEq uu____8882 in
                  (uu____8880, uu____8881) in
                FStar_SMTEncoding_Util.mkImp uu____8877 in
              ([[typing_pred; typing_pred_b]], [xx; aa; bb], uu____8876) in
            mkForall_fuel' (Prims.parse_int "2") uu____8870 in
          (uu____8869, (Some "ref typing is injective"), "ref_injectivity") in
        FStar_SMTEncoding_Term.Assume uu____8865 in
      [uu____8864] in
    uu____8831 :: uu____8862 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8928 =
      let uu____8929 =
        let uu____8933 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8933, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Term.Assume uu____8929 in
    [uu____8928] in
  let mk_and_interp env conj uu____8944 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____8954 =
        let uu____8958 =
          let uu____8960 = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
          [uu____8960] in
        ("Valid", uu____8958) in
      FStar_SMTEncoding_Util.mkApp uu____8954 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8967 =
      let uu____8968 =
        let uu____8972 =
          let uu____8973 =
            let uu____8979 =
              let uu____8980 =
                let uu____8983 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____8983, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8980 in
            ([[valid]], [aa; bb], uu____8979) in
          FStar_SMTEncoding_Util.mkForall uu____8973 in
        (uu____8972, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Term.Assume uu____8968 in
    [uu____8967] in
  let mk_or_interp env disj uu____9007 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9017 =
        let uu____9021 =
          let uu____9023 = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
          [uu____9023] in
        ("Valid", uu____9021) in
      FStar_SMTEncoding_Util.mkApp uu____9017 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9030 =
      let uu____9031 =
        let uu____9035 =
          let uu____9036 =
            let uu____9042 =
              let uu____9043 =
                let uu____9046 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9046, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9043 in
            ([[valid]], [aa; bb], uu____9042) in
          FStar_SMTEncoding_Util.mkForall uu____9036 in
        (uu____9035, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Term.Assume uu____9031 in
    [uu____9030] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let valid =
      let uu____9084 =
        let uu____9088 =
          let uu____9090 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
          [uu____9090] in
        ("Valid", uu____9088) in
      FStar_SMTEncoding_Util.mkApp uu____9084 in
    let uu____9093 =
      let uu____9094 =
        let uu____9098 =
          let uu____9099 =
            let uu____9105 =
              let uu____9106 =
                let uu____9109 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9109, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9106 in
            ([[valid]], [aa; xx1; yy1], uu____9105) in
          FStar_SMTEncoding_Util.mkForall uu____9099 in
        (uu____9098, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Term.Assume uu____9094 in
    [uu____9093] in
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
      let uu____9153 =
        let uu____9157 =
          let uu____9159 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
          [uu____9159] in
        ("Valid", uu____9157) in
      FStar_SMTEncoding_Util.mkApp uu____9153 in
    let uu____9162 =
      let uu____9163 =
        let uu____9167 =
          let uu____9168 =
            let uu____9174 =
              let uu____9175 =
                let uu____9178 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9178, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9175 in
            ([[valid]], [aa; bb; xx1; yy1], uu____9174) in
          FStar_SMTEncoding_Util.mkForall uu____9168 in
        (uu____9167, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Term.Assume uu____9163 in
    [uu____9162] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9216 =
        let uu____9220 =
          let uu____9222 = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
          [uu____9222] in
        ("Valid", uu____9220) in
      FStar_SMTEncoding_Util.mkApp uu____9216 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9229 =
      let uu____9230 =
        let uu____9234 =
          let uu____9235 =
            let uu____9241 =
              let uu____9242 =
                let uu____9245 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9245, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9242 in
            ([[valid]], [aa; bb], uu____9241) in
          FStar_SMTEncoding_Util.mkForall uu____9235 in
        (uu____9234, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Term.Assume uu____9230 in
    [uu____9229] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let valid =
      let uu____9279 =
        let uu____9283 =
          let uu____9285 = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
          [uu____9285] in
        ("Valid", uu____9283) in
      FStar_SMTEncoding_Util.mkApp uu____9279 in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9292 =
      let uu____9293 =
        let uu____9297 =
          let uu____9298 =
            let uu____9304 =
              let uu____9305 =
                let uu____9308 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9308, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9305 in
            ([[valid]], [aa; bb], uu____9304) in
          FStar_SMTEncoding_Util.mkForall uu____9298 in
        (uu____9297, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Term.Assume uu____9293 in
    [uu____9292] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let valid =
      let uu____9338 =
        let uu____9342 =
          let uu____9344 = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
          [uu____9344] in
        ("Valid", uu____9342) in
      FStar_SMTEncoding_Util.mkApp uu____9338 in
    let not_valid_a =
      let uu____9348 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9348 in
    let uu____9350 =
      let uu____9351 =
        let uu____9355 =
          let uu____9356 =
            let uu____9362 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[valid]], [aa], uu____9362) in
          FStar_SMTEncoding_Util.mkForall uu____9356 in
        (uu____9355, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Term.Assume uu____9351 in
    [uu____9350] in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let valid =
      let uu____9398 =
        let uu____9402 =
          let uu____9404 = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b]) in
          [uu____9404] in
        ("Valid", uu____9402) in
      FStar_SMTEncoding_Util.mkApp uu____9398 in
    let valid_b_x =
      let uu____9408 =
        let uu____9412 =
          let uu____9414 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9414] in
        ("Valid", uu____9412) in
      FStar_SMTEncoding_Util.mkApp uu____9408 in
    let uu____9416 =
      let uu____9417 =
        let uu____9421 =
          let uu____9422 =
            let uu____9428 =
              let uu____9429 =
                let uu____9432 =
                  let uu____9433 =
                    let uu____9439 =
                      let uu____9442 =
                        let uu____9444 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9444] in
                      [uu____9442] in
                    let uu____9447 =
                      let uu____9448 =
                        let uu____9451 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9451, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9448 in
                    (uu____9439, [xx1], uu____9447) in
                  FStar_SMTEncoding_Util.mkForall uu____9433 in
                (uu____9432, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9429 in
            ([[valid]], [aa; bb], uu____9428) in
          FStar_SMTEncoding_Util.mkForall uu____9422 in
        (uu____9421, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Term.Assume uu____9417 in
    [uu____9416] in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let valid =
      let uu____9498 =
        let uu____9502 =
          let uu____9504 = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b]) in
          [uu____9504] in
        ("Valid", uu____9502) in
      FStar_SMTEncoding_Util.mkApp uu____9498 in
    let valid_b_x =
      let uu____9508 =
        let uu____9512 =
          let uu____9514 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9514] in
        ("Valid", uu____9512) in
      FStar_SMTEncoding_Util.mkApp uu____9508 in
    let uu____9516 =
      let uu____9517 =
        let uu____9521 =
          let uu____9522 =
            let uu____9528 =
              let uu____9529 =
                let uu____9532 =
                  let uu____9533 =
                    let uu____9539 =
                      let uu____9542 =
                        let uu____9544 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9544] in
                      [uu____9542] in
                    let uu____9547 =
                      let uu____9548 =
                        let uu____9551 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9551, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9548 in
                    (uu____9539, [xx1], uu____9547) in
                  FStar_SMTEncoding_Util.mkExists uu____9533 in
                (uu____9532, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9529 in
            ([[valid]], [aa; bb], uu____9528) in
          FStar_SMTEncoding_Util.mkForall uu____9522 in
        (uu____9521, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Term.Assume uu____9517 in
    [uu____9516] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9587 =
      let uu____9588 =
        let uu____9592 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9593 = varops.mk_unique "typing_range_const" in
        (uu____9592, (Some "Range_const typing"), uu____9593) in
      FStar_SMTEncoding_Term.Assume uu____9588 in
    [uu____9587] in
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
          let uu____9855 =
            FStar_Util.find_opt
              (fun uu____9873  ->
                 match uu____9873 with
                 | (l,uu____9883) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9855 with
          | None  -> []
          | Some (uu____9905,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9942 = encode_function_type_as_formula None None t env in
        match uu____9942 with
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
            let uu____9974 =
              (let uu____9975 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____9975) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____9974
            then
              let uu____9979 = new_term_constant_and_tok_from_lid env lid in
              match uu____9979 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____9991 =
                      let uu____9992 = FStar_Syntax_Subst.compress t_norm in
                      uu____9992.FStar_Syntax_Syntax.n in
                    match uu____9991 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9997) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10014  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10017 -> [] in
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
              (let uu____10026 = prims.is lid in
               if uu____10026
               then
                 let vname = varops.new_fvar lid in
                 let uu____10031 = prims.mk lid vname in
                 match uu____10031 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10046 =
                    let uu____10052 = curried_arrow_formals_comp t_norm in
                    match uu____10052 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10063 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10063
                          then
                            let uu____10064 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___153_10065 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___153_10065.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___153_10065.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___153_10065.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___153_10065.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___153_10065.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___153_10065.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___153_10065.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___153_10065.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___153_10065.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___153_10065.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___153_10065.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___153_10065.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___153_10065.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___153_10065.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___153_10065.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___153_10065.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___153_10065.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___153_10065.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___153_10065.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___153_10065.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___153_10065.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___153_10065.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___153_10065.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10064
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10072 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10072)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10046 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10099 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10099 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10112 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___124_10136  ->
                                     match uu___124_10136 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10139 =
                                           FStar_Util.prefix vars in
                                         (match uu____10139 with
                                          | (uu____10150,(xxsym,uu____10152))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10162 =
                                                let uu____10163 =
                                                  let uu____10167 =
                                                    let uu____10168 =
                                                      let uu____10174 =
                                                        let uu____10175 =
                                                          let uu____10178 =
                                                            let uu____10179 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10179 in
                                                          (vapp, uu____10178) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10175 in
                                                      ([[vapp]], vars,
                                                        uu____10174) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10168 in
                                                  (uu____10167,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10163 in
                                              [uu____10162])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10190 =
                                           FStar_Util.prefix vars in
                                         (match uu____10190 with
                                          | (uu____10201,(xxsym,uu____10203))
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
                                              let uu____10217 =
                                                let uu____10218 =
                                                  let uu____10222 =
                                                    let uu____10223 =
                                                      let uu____10229 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10229) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10223 in
                                                  (uu____10222,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10218 in
                                              [uu____10217])
                                     | uu____10238 -> [])) in
                           let uu____10239 = encode_binders None formals env1 in
                           (match uu____10239 with
                            | (vars,guards,env',decls1,uu____10255) ->
                                let uu____10262 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10267 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10267, decls1)
                                  | Some p ->
                                      let uu____10269 = encode_formula p env' in
                                      (match uu____10269 with
                                       | (g,ds) ->
                                           let uu____10276 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10276,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10262 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10285 =
                                         let uu____10289 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10289) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10285 in
                                     let uu____10294 =
                                       let vname_decl =
                                         let uu____10299 =
                                           let uu____10305 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10310  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10305,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10299 in
                                       let uu____10315 =
                                         let env2 =
                                           let uu___154_10319 = env1 in
                                           {
                                             bindings =
                                               (uu___154_10319.bindings);
                                             depth = (uu___154_10319.depth);
                                             tcenv = (uu___154_10319.tcenv);
                                             warn = (uu___154_10319.warn);
                                             cache = (uu___154_10319.cache);
                                             nolabels =
                                               (uu___154_10319.nolabels);
                                             use_zfuel_name =
                                               (uu___154_10319.use_zfuel_name);
                                             encode_non_total_function_typ
                                           } in
                                         let uu____10320 =
                                           let uu____10321 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10321 in
                                         if uu____10320
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10315 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             FStar_SMTEncoding_Term.Assume
                                               (tok_typing,
                                                 (Some
                                                    "function token typing"),
                                                 (Prims.strcat
                                                    "function_token_typing_"
                                                    vname)) in
                                           let uu____10332 =
                                             match formals with
                                             | [] ->
                                                 let uu____10341 =
                                                   let uu____10342 =
                                                     let uu____10344 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10344 in
                                                   push_free_var env1 lid
                                                     vname uu____10342 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10341)
                                             | uu____10347 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10352 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10352 in
                                                 let name_tok_corr =
                                                   let uu____10354 =
                                                     let uu____10358 =
                                                       let uu____10359 =
                                                         let uu____10365 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10365) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10359 in
                                                     (uu____10358,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Term.Assume
                                                     uu____10354 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10332 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10294 with
                                      | (decls2,env2) ->
                                          let uu____10389 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10394 =
                                              encode_term res_t1 env' in
                                            match uu____10394 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10402 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10402,
                                                  decls) in
                                          (match uu____10389 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10410 =
                                                   let uu____10414 =
                                                     let uu____10415 =
                                                       let uu____10421 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10421) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10415 in
                                                   (uu____10414,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____10410 in
                                               let freshness =
                                                 let uu____10430 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10430
                                                 then
                                                   let uu____10433 =
                                                     let uu____10434 =
                                                       let uu____10440 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10446 =
                                                         varops.next_id () in
                                                       (vname, uu____10440,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10446) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10434 in
                                                   let uu____10448 =
                                                     let uu____10450 =
                                                       pretype_axiom vapp
                                                         vars in
                                                     [uu____10450] in
                                                   uu____10433 :: uu____10448
                                                 else [] in
                                               let g =
                                                 let uu____10454 =
                                                   let uu____10456 =
                                                     let uu____10458 =
                                                       let uu____10460 =
                                                         let uu____10462 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10462 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10460 in
                                                     FStar_List.append decls3
                                                       uu____10458 in
                                                   FStar_List.append decls2
                                                     uu____10456 in
                                                 FStar_List.append decls11
                                                   uu____10454 in
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
          let uu____10484 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10484 with
          | None  ->
              let uu____10507 = encode_free_var env x t t_norm [] in
              (match uu____10507 with
               | (decls,env1) ->
                   let uu____10522 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10522 with
                    | (n1,x',uu____10541) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10553) -> ((n1, x1), [], env)
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
          let uu____10586 = encode_free_var env lid t tt quals in
          match uu____10586 with
          | (decls,env1) ->
              let uu____10597 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10597
              then
                let uu____10601 =
                  let uu____10603 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10603 in
                (uu____10601, env1)
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
             (fun uu____10631  ->
                fun lb  ->
                  match uu____10631 with
                  | (decls,env1) ->
                      let uu____10643 =
                        let uu____10647 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10647
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10643 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10661 = FStar_Syntax_Util.head_and_args t in
    match uu____10661 with
    | (hd1,args) ->
        let uu____10687 =
          let uu____10688 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10688.FStar_Syntax_Syntax.n in
        (match uu____10687 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10692,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10705 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10720  ->
      fun quals  ->
        match uu____10720 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10769 = FStar_Util.first_N nbinders formals in
              match uu____10769 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10809  ->
                         fun uu____10810  ->
                           match (uu____10809, uu____10810) with
                           | ((formal,uu____10820),(binder,uu____10822)) ->
                               let uu____10827 =
                                 let uu____10832 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10832) in
                               FStar_Syntax_Syntax.NT uu____10827) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10837 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10851  ->
                              match uu____10851 with
                              | (x,i) ->
                                  let uu____10858 =
                                    let uu___155_10859 = x in
                                    let uu____10860 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___155_10859.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___155_10859.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10860
                                    } in
                                  (uu____10858, i))) in
                    FStar_All.pipe_right uu____10837
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10872 =
                      let uu____10874 =
                        let uu____10875 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10875.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10874 in
                    let uu____10879 =
                      let uu____10880 = FStar_Syntax_Subst.compress body in
                      let uu____10881 =
                        let uu____10882 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10882 in
                      FStar_Syntax_Syntax.extend_app_n uu____10880
                        uu____10881 in
                    uu____10879 uu____10872 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10924 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10924
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___156_10925 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___156_10925.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___156_10925.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___156_10925.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___156_10925.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___156_10925.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___156_10925.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___156_10925.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___156_10925.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___156_10925.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___156_10925.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___156_10925.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___156_10925.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___156_10925.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___156_10925.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___156_10925.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___156_10925.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___156_10925.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___156_10925.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___156_10925.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___156_10925.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___156_10925.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___156_10925.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___156_10925.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____10946 = FStar_Syntax_Util.abs_formals e in
                match uu____10946 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____10995::uu____10996 ->
                         let uu____11004 =
                           let uu____11005 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11005.FStar_Syntax_Syntax.n in
                         (match uu____11004 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11032 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11032 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11058 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11058
                                   then
                                     let uu____11076 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11076 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11122  ->
                                                   fun uu____11123  ->
                                                     match (uu____11122,
                                                             uu____11123)
                                                     with
                                                     | ((x,uu____11133),
                                                        (b,uu____11135)) ->
                                                         let uu____11140 =
                                                           let uu____11145 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11145) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11140)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11147 =
                                            let uu____11158 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11158) in
                                          (uu____11147, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11193 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11193 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11245) ->
                              let uu____11250 =
                                let uu____11261 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11261 in
                              (uu____11250, true)
                          | uu____11294 when Prims.op_Negation norm1 ->
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
                          | uu____11296 ->
                              let uu____11297 =
                                let uu____11298 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11299 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11298
                                  uu____11299 in
                              failwith uu____11297)
                     | uu____11312 ->
                         let uu____11313 =
                           let uu____11314 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11314.FStar_Syntax_Syntax.n in
                         (match uu____11313 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11341 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11341 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11359 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11359 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11407 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11435 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11435
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11442 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11483  ->
                            fun lb  ->
                              match uu____11483 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11534 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11534
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11537 =
                                      let uu____11545 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11545
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11537 with
                                    | (tok,decl,env2) ->
                                        let uu____11570 =
                                          let uu____11577 =
                                            let uu____11583 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11583, tok) in
                                          uu____11577 :: toks in
                                        (uu____11570, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11442 with
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
                        | uu____11685 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11690 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11690 vars)
                            else
                              (let uu____11692 =
                                 let uu____11696 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11696) in
                               FStar_SMTEncoding_Util.mkApp uu____11692) in
                      let uu____11701 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___125_11703  ->
                                 match uu___125_11703 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11704 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11707 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11707))) in
                      if uu____11701
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11727;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11729;
                                FStar_Syntax_Syntax.lbeff = uu____11730;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11771 =
                                 FStar_Syntax_Subst.univ_var_opening uvs in
                               (match uu____11771 with
                                | (univ_subst,univ_vars1) ->
                                    let env' =
                                      let uu___159_11786 = env1 in
                                      let uu____11787 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1.tcenv univ_vars1 in
                                      {
                                        bindings = (uu___159_11786.bindings);
                                        depth = (uu___159_11786.depth);
                                        tcenv = uu____11787;
                                        warn = (uu___159_11786.warn);
                                        cache = (uu___159_11786.cache);
                                        nolabels = (uu___159_11786.nolabels);
                                        use_zfuel_name =
                                          (uu___159_11786.use_zfuel_name);
                                        encode_non_total_function_typ =
                                          (uu___159_11786.encode_non_total_function_typ)
                                      } in
                                    let t_norm1 =
                                      FStar_Syntax_Subst.subst univ_subst
                                        t_norm in
                                    let e1 =
                                      let uu____11790 =
                                        FStar_Syntax_Subst.subst univ_subst e in
                                      FStar_Syntax_Subst.compress uu____11790 in
                                    let uu____11791 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11791 with
                                     | ((binders,body,uu____11803,uu____11804),curry)
                                         ->
                                         ((let uu____11811 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11811
                                           then
                                             let uu____11812 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11813 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11812 uu____11813
                                           else ());
                                          (let uu____11815 =
                                             encode_binders None binders env' in
                                           match uu____11815 with
                                           | (vars,guards,env'1,binder_decls,uu____11831)
                                               ->
                                               let body1 =
                                                 let uu____11839 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11839
                                                 then
                                                   reify_body env'1.tcenv
                                                     body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11842 =
                                                 let uu____11847 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11847
                                                 then
                                                   let uu____11853 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11854 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11853, uu____11854)
                                                 else
                                                   (let uu____11860 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11860)) in
                                               (match uu____11842 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11874 =
                                                        let uu____11878 =
                                                          let uu____11879 =
                                                            let uu____11885 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11885) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11879 in
                                                        let uu____11891 =
                                                          let uu____11893 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11893 in
                                                        (uu____11878,
                                                          uu____11891,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Term.Assume
                                                        uu____11874 in
                                                    let uu____11895 =
                                                      let uu____11897 =
                                                        let uu____11899 =
                                                          let uu____11901 =
                                                            let uu____11903 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11903 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11901 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11899 in
                                                      FStar_List.append
                                                        decls1 uu____11897 in
                                                    (uu____11895, env1))))))
                           | uu____11906 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11925 = varops.fresh "fuel" in
                             (uu____11925, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____11928 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____11967  ->
                                     fun uu____11968  ->
                                       match (uu____11967, uu____11968) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12050 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12050 in
                                           let gtok =
                                             let uu____12052 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12052 in
                                           let env3 =
                                             let uu____12054 =
                                               let uu____12056 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12056 in
                                             push_free_var env2 flid gtok
                                               uu____12054 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____11928 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12140
                                 t_norm uu____12142 =
                                 match (uu____12140, uu____12142) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12167;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12168;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12185 =
                                       FStar_Syntax_Subst.univ_var_opening
                                         uvs in
                                     (match uu____12185 with
                                      | (univ_subst,univ_vars1) ->
                                          let env' =
                                            let uu___160_12202 = env2 in
                                            let uu____12203 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env2.tcenv univ_vars1 in
                                            {
                                              bindings =
                                                (uu___160_12202.bindings);
                                              depth = (uu___160_12202.depth);
                                              tcenv = uu____12203;
                                              warn = (uu___160_12202.warn);
                                              cache = (uu___160_12202.cache);
                                              nolabels =
                                                (uu___160_12202.nolabels);
                                              use_zfuel_name =
                                                (uu___160_12202.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___160_12202.encode_non_total_function_typ)
                                            } in
                                          let t_norm1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst t_norm in
                                          let e1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst e in
                                          ((let uu____12207 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12207
                                            then
                                              let uu____12208 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12209 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12210 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12208 uu____12209
                                                uu____12210
                                            else ());
                                           (let uu____12212 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12212 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12234 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12234
                                                  then
                                                    let uu____12235 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12236 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12237 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12238 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12235 uu____12236
                                                      uu____12237 uu____12238
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12242 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12242 with
                                                  | (vars,guards,env'1,binder_decls,uu____12260)
                                                      ->
                                                      let decl_g =
                                                        let uu____12268 =
                                                          let uu____12274 =
                                                            let uu____12276 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12276 in
                                                          (g, uu____12274,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12268 in
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
                                                        let uu____12291 =
                                                          let uu____12295 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12295) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12291 in
                                                      let gsapp =
                                                        let uu____12301 =
                                                          let uu____12305 =
                                                            let uu____12307 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12307 ::
                                                              vars_tm in
                                                          (g, uu____12305) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12301 in
                                                      let gmax =
                                                        let uu____12311 =
                                                          let uu____12315 =
                                                            let uu____12317 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12317 ::
                                                              vars_tm in
                                                          (g, uu____12315) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12311 in
                                                      let body1 =
                                                        let uu____12321 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12321
                                                        then
                                                          reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12323 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12323 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12334
                                                               =
                                                               let uu____12338
                                                                 =
                                                                 let uu____12339
                                                                   =
                                                                   let uu____12347
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
                                                                    uu____12347) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12339 in
                                                               let uu____12358
                                                                 =
                                                                 let uu____12360
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12360 in
                                                               (uu____12338,
                                                                 uu____12358,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12334 in
                                                           let eqn_f =
                                                             let uu____12363
                                                               =
                                                               let uu____12367
                                                                 =
                                                                 let uu____12368
                                                                   =
                                                                   let uu____12374
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12374) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12368 in
                                                               (uu____12367,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12363 in
                                                           let eqn_g' =
                                                             let uu____12382
                                                               =
                                                               let uu____12386
                                                                 =
                                                                 let uu____12387
                                                                   =
                                                                   let uu____12393
                                                                    =
                                                                    let uu____12394
                                                                    =
                                                                    let uu____12397
                                                                    =
                                                                    let uu____12398
                                                                    =
                                                                    let uu____12402
                                                                    =
                                                                    let uu____12404
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12404
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12402) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12398 in
                                                                    (gsapp,
                                                                    uu____12397) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12394 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12393) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12387 in
                                                               (uu____12386,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12382 in
                                                           let uu____12416 =
                                                             let uu____12421
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12421
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12438)
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
                                                                    let uu____12453
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12453
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12456
                                                                    =
                                                                    let uu____12460
                                                                    =
                                                                    let uu____12461
                                                                    =
                                                                    let uu____12467
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12467) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12461 in
                                                                    (uu____12460,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Term.Assume
                                                                    uu____12456 in
                                                                 let uu____12478
                                                                   =
                                                                   let uu____12482
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12482
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12490
                                                                    =
                                                                    let uu____12492
                                                                    =
                                                                    let uu____12493
                                                                    =
                                                                    let uu____12497
                                                                    =
                                                                    let uu____12498
                                                                    =
                                                                    let uu____12504
                                                                    =
                                                                    let uu____12505
                                                                    =
                                                                    let uu____12508
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12508,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12505 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12504) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12498 in
                                                                    (uu____12497,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12493 in
                                                                    [uu____12492] in
                                                                    (d3,
                                                                    uu____12490) in
                                                                 (match uu____12478
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12416
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
                               let uu____12543 =
                                 let uu____12550 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12582  ->
                                      fun uu____12583  ->
                                        match (uu____12582, uu____12583) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12659 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12659 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12550 in
                               (match uu____12543 with
                                | (decls2,eqns,env01) ->
                                    let uu____12699 =
                                      let isDeclFun uu___126_12707 =
                                        match uu___126_12707 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12708 -> true
                                        | uu____12714 -> false in
                                      let uu____12715 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12715
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12699 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12742 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12742
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
      (let uu____12775 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____12775
       then
         let uu____12776 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
           uu____12776
       else ());
      (let nm =
         let uu____12779 = FStar_Syntax_Util.lid_of_sigelt se in
         match uu____12779 with | None  -> "" | Some l -> l.FStar_Ident.str in
       let uu____12782 = encode_sigelt' env se in
       match uu____12782 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12791 =
                  let uu____12793 =
                    let uu____12794 = FStar_Util.format1 "<Skipped %s/>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12794 in
                  [uu____12793] in
                (uu____12791, e)
            | uu____12796 ->
                let uu____12797 =
                  let uu____12799 =
                    let uu____12801 =
                      let uu____12802 =
                        FStar_Util.format1 "<Start encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12802 in
                    uu____12801 :: g in
                  let uu____12803 =
                    let uu____12805 =
                      let uu____12806 =
                        FStar_Util.format1 "</end encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12806 in
                    [uu____12805] in
                  FStar_List.append uu____12799 uu____12803 in
                (uu____12797, e)))
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12814 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12823 =
            let uu____12824 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12824 Prims.op_Negation in
          if uu____12823
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12844 ->
                   let uu____12845 =
                     let uu____12848 =
                       let uu____12849 =
                         let uu____12864 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12864) in
                       FStar_Syntax_Syntax.Tm_abs uu____12849 in
                     FStar_Syntax_Syntax.mk uu____12848 in
                   uu____12845 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____12917 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____12917 with
               | (aname,atok,env2) ->
                   let uu____12927 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____12927 with
                    | (formals,uu____12937) ->
                        let uu____12944 =
                          let uu____12947 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____12947 env2 in
                        (match uu____12944 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____12955 =
                                 let uu____12956 =
                                   let uu____12962 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____12970  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____12962,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____12956 in
                               [uu____12955;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____12977 =
                               let aux uu____13006 uu____13007 =
                                 match (uu____13006, uu____13007) with
                                 | ((bv,uu____13034),(env3,acc_sorts,acc)) ->
                                     let uu____13055 = gen_term_var env3 bv in
                                     (match uu____13055 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____12977 with
                              | (uu____13093,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13107 =
                                      let uu____13111 =
                                        let uu____13112 =
                                          let uu____13118 =
                                            let uu____13119 =
                                              let uu____13122 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13122) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13119 in
                                          ([[app]], xs_sorts, uu____13118) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13112 in
                                      (uu____13111, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Term.Assume uu____13107 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13134 =
                                      let uu____13138 =
                                        let uu____13139 =
                                          let uu____13145 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13145) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13139 in
                                      (uu____13138,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Term.Assume uu____13134 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13155 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13155 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____13171,uu____13172,uu____13173) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13176 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13176 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13187,t,quals) ->
          let will_encode_definition =
            let uu____13193 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___127_13195  ->
                      match uu___127_13195 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13198 -> false)) in
            Prims.op_Negation uu____13193 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13204 = encode_top_level_val env fv t quals in
             match uu____13204 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13216 =
                   let uu____13218 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13218 in
                 (uu____13216, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____13223) ->
          let uu____13226 = encode_formula f env in
          (match uu____13226 with
           | (f1,decls) ->
               let g =
                 let uu____13235 =
                   let uu____13236 =
                     let uu____13240 =
                       let uu____13242 =
                         let uu____13243 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13243 in
                       Some uu____13242 in
                     let uu____13244 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13240, uu____13244) in
                   FStar_SMTEncoding_Term.Assume uu____13236 in
                 [uu____13235] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13248,quals,uu____13250) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13258 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13265 =
                       let uu____13270 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13270.FStar_Syntax_Syntax.fv_name in
                     uu____13265.FStar_Syntax_Syntax.v in
                   let uu____13274 =
                     let uu____13275 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13275 in
                   if uu____13274
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
                     let uu____13294 = encode_sigelt' env1 val_decl in
                     match uu____13294 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13258 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13311,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13313;
                          FStar_Syntax_Syntax.lbtyp = uu____13314;
                          FStar_Syntax_Syntax.lbeff = uu____13315;
                          FStar_Syntax_Syntax.lbdef = uu____13316;_}::[]),uu____13317,uu____13318,uu____13319)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13335 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13335 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let valid_b2t_x =
                 let uu____13353 =
                   let uu____13357 =
                     let uu____13359 =
                       FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
                     [uu____13359] in
                   ("Valid", uu____13357) in
                 FStar_SMTEncoding_Util.mkApp uu____13353 in
               let decls =
                 let uu____13364 =
                   let uu____13366 =
                     let uu____13367 =
                       let uu____13371 =
                         let uu____13372 =
                           let uu____13378 =
                             let uu____13379 =
                               let uu____13382 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13382) in
                             FStar_SMTEncoding_Util.mkEq uu____13379 in
                           ([[valid_b2t_x]], [xx], uu____13378) in
                         FStar_SMTEncoding_Util.mkForall uu____13372 in
                       (uu____13371, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Term.Assume uu____13367 in
                   [uu____13366] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13364 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let
          (uu____13399,uu____13400,quals,uu____13402) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___128_13410  ->
                  match uu___128_13410 with
                  | FStar_Syntax_Syntax.Discriminator uu____13411 -> true
                  | uu____13412 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13414,lids,quals,uu____13417) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13426 =
                     let uu____13427 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13427.FStar_Ident.idText in
                   uu____13426 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___129_13429  ->
                     match uu___129_13429 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13430 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13433,quals,uu____13435) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___130_13447  ->
                  match uu___130_13447 with
                  | FStar_Syntax_Syntax.Projector uu____13448 -> true
                  | uu____13451 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13458 = try_lookup_free_var env l in
          (match uu____13458 with
           | Some uu____13462 -> ([], env)
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
          ((is_rec,bindings),uu____13471,quals,uu____13473) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13487,uu____13488) ->
          let uu____13495 = encode_signature env ses in
          (match uu____13495 with
           | (g,env1) ->
               let uu____13505 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___131_13515  ->
                         match uu___131_13515 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13516,Some "inversion axiom",uu____13517)
                             -> false
                         | uu____13519 -> true)) in
               (match uu____13505 with
                | (g',inversions) ->
                    let uu____13528 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___132_13538  ->
                              match uu___132_13538 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13539 ->
                                  true
                              | uu____13545 -> false)) in
                    (match uu____13528 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13556,tps,k,uu____13559,datas,quals) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___133_13570  ->
                    match uu___133_13570 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13571 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13578 = c in
              match uu____13578 with
              | (name,args,uu____13582,uu____13583,uu____13584) ->
                  let uu____13587 =
                    let uu____13588 =
                      let uu____13594 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13601  ->
                                match uu____13601 with
                                | (uu____13605,sort,uu____13607) -> sort)) in
                      (name, uu____13594, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13588 in
                  [uu____13587]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13625 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13628 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13628 FStar_Option.isNone)) in
            if uu____13625
            then []
            else
              (let uu____13645 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13645 with
               | (xxsym,xx) ->
                   let uu____13651 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13662  ->
                             fun l  ->
                               match uu____13662 with
                               | (out,decls) ->
                                   let uu____13674 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13674 with
                                    | (uu____13680,data_t) ->
                                        let uu____13682 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13682 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13711 =
                                                 let uu____13712 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13712.FStar_Syntax_Syntax.n in
                                               match uu____13711 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13720,indices) ->
                                                   indices
                                               | uu____13736 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13748  ->
                                                         match uu____13748
                                                         with
                                                         | (x,uu____13752) ->
                                                             let uu____13753
                                                               =
                                                               let uu____13754
                                                                 =
                                                                 let uu____13758
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13758,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13754 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13753)
                                                    env) in
                                             let uu____13760 =
                                               encode_args indices env1 in
                                             (match uu____13760 with
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
                                                      let uu____13780 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13788
                                                                 =
                                                                 let uu____13791
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13791,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13788)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13780
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13793 =
                                                      let uu____13794 =
                                                        let uu____13797 =
                                                          let uu____13798 =
                                                            let uu____13801 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13801,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13798 in
                                                        (out, uu____13797) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13794 in
                                                    (uu____13793,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13651 with
                    | (data_ax,decls) ->
                        let uu____13809 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13809 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13820 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13820 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13823 =
                                 let uu____13827 =
                                   let uu____13828 =
                                     let uu____13834 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13842 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13834,
                                       uu____13842) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13828 in
                                 let uu____13850 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13827, (Some "inversion axiom"),
                                   uu____13850) in
                               FStar_SMTEncoding_Term.Assume uu____13823 in
                             let pattern_guarded_inversion =
                               let uu____13854 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13854
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13862 =
                                   let uu____13863 =
                                     let uu____13867 =
                                       let uu____13868 =
                                         let uu____13874 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13882 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13874, uu____13882) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13868 in
                                     let uu____13890 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13867, (Some "inversion axiom"),
                                       uu____13890) in
                                   FStar_SMTEncoding_Term.Assume uu____13863 in
                                 [uu____13862]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13893 =
            let uu____13901 =
              let uu____13902 = FStar_Syntax_Subst.compress k in
              uu____13902.FStar_Syntax_Syntax.n in
            match uu____13901 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13931 -> (tps, k) in
          (match uu____13893 with
           | (formals,res) ->
               let uu____13946 = FStar_Syntax_Subst.open_term formals res in
               (match uu____13946 with
                | (formals1,res1) ->
                    let uu____13953 = encode_binders None formals1 env in
                    (match uu____13953 with
                     | (vars,guards,env',binder_decls,uu____13968) ->
                         let uu____13975 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____13975 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____13988 =
                                  let uu____13992 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____13992) in
                                FStar_SMTEncoding_Util.mkApp uu____13988 in
                              let uu____13997 =
                                let tname_decl =
                                  let uu____14003 =
                                    let uu____14004 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14019  ->
                                              match uu____14019 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14027 = varops.next_id () in
                                    (tname, uu____14004,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14027, false) in
                                  constructor_or_logic_type_decl uu____14003 in
                                let uu____14032 =
                                  match vars with
                                  | [] ->
                                      let uu____14039 =
                                        let uu____14040 =
                                          let uu____14042 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14042 in
                                        push_free_var env1 t tname
                                          uu____14040 in
                                      ([], uu____14039)
                                  | uu____14046 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14052 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14052 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14061 =
                                          let uu____14065 =
                                            let uu____14066 =
                                              let uu____14074 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14074) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14066 in
                                          (uu____14065,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____14061 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14032 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____13997 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14097 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14097 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14111 =
                                               let uu____14112 =
                                                 let uu____14116 =
                                                   let uu____14117 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14117 in
                                                 (uu____14116,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14112 in
                                             [uu____14111]
                                           else [] in
                                         let uu____14120 =
                                           let uu____14122 =
                                             let uu____14124 =
                                               let uu____14125 =
                                                 let uu____14129 =
                                                   let uu____14130 =
                                                     let uu____14136 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14136) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14130 in
                                                 (uu____14129, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14125 in
                                             [uu____14124] in
                                           FStar_List.append karr uu____14122 in
                                         FStar_List.append decls1 uu____14120 in
                                   let aux =
                                     let uu____14145 =
                                       let uu____14147 =
                                         inversion_axioms tapp vars in
                                       let uu____14149 =
                                         let uu____14151 =
                                           pretype_axiom tapp vars in
                                         [uu____14151] in
                                       FStar_List.append uu____14147
                                         uu____14149 in
                                     FStar_List.append kindingAx uu____14145 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14156,uu____14157,uu____14158,uu____14159,uu____14160,uu____14161)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14168,t,uu____14170,n_tps,quals,uu____14173) ->
          let uu____14178 = new_term_constant_and_tok_from_lid env d in
          (match uu____14178 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14189 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14189 with
                | (formals,t_res) ->
                    let uu____14211 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14211 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14220 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14220 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14258 =
                                            mk_term_projector_name d x in
                                          (uu____14258,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14260 =
                                  let uu____14270 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14270, true) in
                                FStar_All.pipe_right uu____14260
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
                              let uu____14292 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14292 with
                               | (tok_typing,decls3) ->
                                   let uu____14299 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14299 with
                                    | (vars',guards',env'',decls_formals,uu____14314)
                                        ->
                                        let uu____14321 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14321 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14340 ->
                                                   let uu____14344 =
                                                     let uu____14345 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14345 in
                                                   [uu____14344] in
                                             let encode_elim uu____14352 =
                                               let uu____14353 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14353 with
                                               | (head1,args) ->
                                                   let uu____14382 =
                                                     let uu____14383 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14383.FStar_Syntax_Syntax.n in
                                                   (match uu____14382 with
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
                                                        let uu____14401 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14401
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
                                                                 | uu____14427
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14435
                                                                    =
                                                                    let uu____14436
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14436 in
                                                                    if
                                                                    uu____14435
                                                                    then
                                                                    let uu____14443
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14443]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14445
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14458
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14458
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14480
                                                                    =
                                                                    let uu____14484
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14484 in
                                                                    (match uu____14480
                                                                    with
                                                                    | 
                                                                    (uu____14491,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14497
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14497
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14499
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14499
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
                                                             (match uu____14445
                                                              with
                                                              | (uu____14507,arg_vars,elim_eqns_or_guards,uu____14510)
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
                                                                    let uu____14529
                                                                    =
                                                                    let uu____14533
                                                                    =
                                                                    let uu____14534
                                                                    =
                                                                    let uu____14540
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14546
                                                                    =
                                                                    let uu____14547
                                                                    =
                                                                    let uu____14550
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14550) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14547 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14540,
                                                                    uu____14546) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14534 in
                                                                    (uu____14533,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14529 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14563
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14563,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14565
                                                                    =
                                                                    let uu____14569
                                                                    =
                                                                    let uu____14570
                                                                    =
                                                                    let uu____14576
                                                                    =
                                                                    let uu____14579
                                                                    =
                                                                    let uu____14581
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14581] in
                                                                    [uu____14579] in
                                                                    let uu____14584
                                                                    =
                                                                    let uu____14585
                                                                    =
                                                                    let uu____14588
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14589
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14588,
                                                                    uu____14589) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14585 in
                                                                    (uu____14576,
                                                                    [x],
                                                                    uu____14584) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14570 in
                                                                    let uu____14599
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14569,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14599) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14565
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14604
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
                                                                    (let uu____14619
                                                                    =
                                                                    let uu____14620
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14620
                                                                    dapp1 in
                                                                    [uu____14619]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14604
                                                                    FStar_List.flatten in
                                                                    let uu____14624
                                                                    =
                                                                    let uu____14628
                                                                    =
                                                                    let uu____14629
                                                                    =
                                                                    let uu____14635
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14641
                                                                    =
                                                                    let uu____14642
                                                                    =
                                                                    let uu____14645
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14645) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14642 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14635,
                                                                    uu____14641) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14629 in
                                                                    (uu____14628,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14624) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14655 ->
                                                        ((let uu____14657 =
                                                            let uu____14658 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14659 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14658
                                                              uu____14659 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14657);
                                                         ([], []))) in
                                             let uu____14662 = encode_elim () in
                                             (match uu____14662 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14674 =
                                                      let uu____14676 =
                                                        let uu____14678 =
                                                          let uu____14680 =
                                                            let uu____14682 =
                                                              let uu____14683
                                                                =
                                                                let uu____14689
                                                                  =
                                                                  let uu____14691
                                                                    =
                                                                    let uu____14692
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14692 in
                                                                  Some
                                                                    uu____14691 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14689) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14683 in
                                                            [uu____14682] in
                                                          let uu____14695 =
                                                            let uu____14697 =
                                                              let uu____14699
                                                                =
                                                                let uu____14701
                                                                  =
                                                                  let uu____14703
                                                                    =
                                                                    let uu____14705
                                                                    =
                                                                    let uu____14707
                                                                    =
                                                                    let uu____14708
                                                                    =
                                                                    let uu____14712
                                                                    =
                                                                    let uu____14713
                                                                    =
                                                                    let uu____14719
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14719) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14713 in
                                                                    (uu____14712,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14708 in
                                                                    let uu____14726
                                                                    =
                                                                    let uu____14728
                                                                    =
                                                                    let uu____14729
                                                                    =
                                                                    let uu____14733
                                                                    =
                                                                    let uu____14734
                                                                    =
                                                                    let uu____14740
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14746
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14740,
                                                                    uu____14746) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14734 in
                                                                    (uu____14733,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14729 in
                                                                    [uu____14728] in
                                                                    uu____14707
                                                                    ::
                                                                    uu____14726 in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14705 in
                                                                  FStar_List.append
                                                                    uu____14703
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14701 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14699 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14697 in
                                                          FStar_List.append
                                                            uu____14680
                                                            uu____14695 in
                                                        FStar_List.append
                                                          decls3 uu____14678 in
                                                      FStar_List.append
                                                        decls2 uu____14676 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14674 in
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
           (fun uu____14767  ->
              fun se  ->
                match uu____14767 with
                | (g,env1) ->
                    let uu____14779 = encode_sigelt env1 se in
                    (match uu____14779 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14815 =
        match uu____14815 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14833 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14838 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14838
                   then
                     let uu____14839 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14840 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14841 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14839 uu____14840 uu____14841
                   else ());
                  (let uu____14843 = encode_term t1 env1 in
                   match uu____14843 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14853 =
                         let uu____14857 =
                           let uu____14858 =
                             let uu____14859 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____14859
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____14858 in
                         new_term_constant_from_string env1 x uu____14857 in
                       (match uu____14853 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____14870 = FStar_Options.log_queries () in
                              if uu____14870
                              then
                                let uu____14872 =
                                  let uu____14873 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____14874 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____14875 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14873 uu____14874 uu____14875 in
                                Some uu____14872
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14886,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____14895 = encode_free_var env1 fv t t_norm [] in
                 (match uu____14895 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____14914 = encode_sigelt env1 se in
                 (match uu____14914 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____14924 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____14924 with | (uu____14936,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____14981  ->
            match uu____14981 with
            | (l,uu____14988,uu____14989) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15010  ->
            match uu____15010 with
            | (l,uu____15018,uu____15019) ->
                let uu____15024 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____15025 =
                  let uu____15027 =
                    let uu____15028 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15028 in
                  [uu____15027] in
                uu____15024 :: uu____15025)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15039 =
      let uu____15041 =
        let uu____15042 = FStar_Util.smap_create (Prims.parse_int "100") in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15042;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true
        } in
      [uu____15041] in
    FStar_ST.write last_env uu____15039
let get_env: FStar_TypeChecker_Env.env -> env_t =
  fun tcenv  ->
    let uu____15060 = FStar_ST.read last_env in
    match uu____15060 with
    | [] -> failwith "No env; call init first!"
    | e::uu____15066 ->
        let uu___161_15068 = e in
        {
          bindings = (uu___161_15068.bindings);
          depth = (uu___161_15068.depth);
          tcenv;
          warn = (uu___161_15068.warn);
          cache = (uu___161_15068.cache);
          nolabels = (uu___161_15068.nolabels);
          use_zfuel_name = (uu___161_15068.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___161_15068.encode_non_total_function_typ)
        }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15072 = FStar_ST.read last_env in
    match uu____15072 with
    | [] -> failwith "Empty env stack"
    | uu____15077::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15085  ->
    let uu____15086 = FStar_ST.read last_env in
    match uu____15086 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___162_15107 = hd1 in
          {
            bindings = (uu___162_15107.bindings);
            depth = (uu___162_15107.depth);
            tcenv = (uu___162_15107.tcenv);
            warn = (uu___162_15107.warn);
            cache = refs;
            nolabels = (uu___162_15107.nolabels);
            use_zfuel_name = (uu___162_15107.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_15107.encode_non_total_function_typ)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15113  ->
    let uu____15114 = FStar_ST.read last_env in
    match uu____15114 with
    | [] -> failwith "Popping an empty stack"
    | uu____15119::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15127  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15130  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15133  ->
    let uu____15134 = FStar_ST.read last_env in
    match uu____15134 with
    | hd1::uu____15140::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15146 -> failwith "Impossible"
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
        let uu____15191 = FStar_Options.log_queries () in
        if uu____15191
        then
          let uu____15193 =
            let uu____15194 =
              let uu____15195 =
                let uu____15196 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15196 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15195 in
            FStar_SMTEncoding_Term.Caption uu____15194 in
          uu____15193 :: decls
        else decls in
      let env = get_env tcenv in
      let uu____15203 = encode_sigelt env se in
      match uu____15203 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15209 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15209))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15220 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15220
       then
         let uu____15221 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15221
       else ());
      (let env = get_env tcenv in
       let uu____15226 =
         encode_signature
           (let uu___163_15230 = env in
            {
              bindings = (uu___163_15230.bindings);
              depth = (uu___163_15230.depth);
              tcenv = (uu___163_15230.tcenv);
              warn = false;
              cache = (uu___163_15230.cache);
              nolabels = (uu___163_15230.nolabels);
              use_zfuel_name = (uu___163_15230.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___163_15230.encode_non_total_function_typ)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15226 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15242 = FStar_Options.log_queries () in
             if uu____15242
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___164_15247 = env1 in
               {
                 bindings = (uu___164_15247.bindings);
                 depth = (uu___164_15247.depth);
                 tcenv = (uu___164_15247.tcenv);
                 warn = true;
                 cache = (uu___164_15247.cache);
                 nolabels = (uu___164_15247.nolabels);
                 use_zfuel_name = (uu___164_15247.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___164_15247.encode_non_total_function_typ)
               });
            (let uu____15249 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15249
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
        (let uu____15284 =
           let uu____15285 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15285.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15284);
        (let env = get_env tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15293 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15314 = aux rest in
                 (match uu____15314 with
                  | (out,rest1) ->
                      let t =
                        let uu____15332 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15332 with
                        | Some uu____15336 ->
                            let uu____15337 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15337
                              x.FStar_Syntax_Syntax.sort
                        | uu____15338 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15341 =
                        let uu____15343 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___165_15344 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___165_15344.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___165_15344.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15343 :: out in
                      (uu____15341, rest1))
             | uu____15347 -> ([], bindings1) in
           let uu____15351 = aux bindings in
           match uu____15351 with
           | (closing,bindings1) ->
               let uu____15365 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15365, bindings1) in
         match uu____15293 with
         | (q1,bindings1) ->
             let uu____15378 =
               let uu____15381 =
                 FStar_List.filter
                   (fun uu___134_15383  ->
                      match uu___134_15383 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15384 ->
                          false
                      | uu____15388 -> true) bindings1 in
               encode_env_bindings env uu____15381 in
             (match uu____15378 with
              | (env_decls,env1) ->
                  ((let uu____15399 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15399
                    then
                      let uu____15400 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15400
                    else ());
                   (let uu____15402 = encode_formula q1 env1 in
                    match uu____15402 with
                    | (phi,qdecls) ->
                        let uu____15414 =
                          let uu____15417 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15417 phi in
                        (match uu____15414 with
                         | (labels,phi1) ->
                             let uu____15427 = encode_labels labels in
                             (match uu____15427 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15448 =
                                      let uu____15452 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15453 =
                                        varops.mk_unique "@query" in
                                      (uu____15452, (Some "query"),
                                        uu____15453) in
                                    FStar_SMTEncoding_Term.Assume uu____15448 in
                                  let suffix =
                                    let uu____15457 =
                                      let uu____15459 =
                                        let uu____15461 =
                                          FStar_Options.print_z3_statistics
                                            () in
                                        if uu____15461
                                        then
                                          [FStar_SMTEncoding_Term.PrintStats]
                                        else [] in
                                      FStar_List.append uu____15459
                                        [FStar_SMTEncoding_Term.Echo "Done!"] in
                                    FStar_List.append label_suffix
                                      uu____15457 in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env = get_env tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15474 = encode_formula q env in
       match uu____15474 with
       | (f,uu____15478) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15480) -> true
             | uu____15483 -> false)))