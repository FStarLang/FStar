open Prims
let add_fuel x tl1 =
  let uu____16 = FStar_Options.unthrottle_inductives ()  in
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
            let uu____121 = l1.FStar_Syntax_Syntax.comp ()  in
            FStar_Syntax_Subst.subst_comp s uu____121  in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____118  in
        FStar_Util.Inl uu____117  in
      Some uu____114
  | uu____126 -> l 
let escape : Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_' 
let mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___135_140 = a  in
        let uu____141 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___135_140.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___135_140.FStar_Syntax_Syntax.sort)
        }  in
      let uu____142 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____142
  
let primitive_projector_by_pos :
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
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____156  in
        let uu____157 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____157 with
        | (uu____160,t) ->
            let uu____162 =
              let uu____163 = FStar_Syntax_Subst.compress t  in
              uu____163.FStar_Syntax_Syntax.n  in
            (match uu____162 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____178 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____178 with
                  | (binders,uu____182) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid (Prims.fst b)))
             | uu____193 -> fail ())
  
let mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____200 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____200
  
let mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____207 =
        let uu____210 = mk_term_projector_name lid a  in
        (uu____210,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____207
  
let mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____217 =
        let uu____220 = mk_term_projector_name_by_pos lid i  in
        (uu____220,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____217
  
let mk_data_tester env l x =
  FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x 
type varops_t =
  {
  push: Prims.unit -> Prims.unit ;
  pop: Prims.unit -> Prims.unit ;
  mark: Prims.unit -> Prims.unit ;
  reset_mark: Prims.unit -> Prims.unit ;
  commit_mark: Prims.unit -> Prims.unit ;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string ;
  new_fvar: FStar_Ident.lident -> Prims.string ;
  fresh: Prims.string -> Prims.string ;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term ;
  next_id: Prims.unit -> Prims.int ;
  mk_unique: Prims.string -> Prims.string }
let varops : varops_t =
  let initial_ctr = (Prims.parse_int "100")  in
  let ctr = FStar_Util.mk_ref initial_ctr  in
  let new_scope uu____410 =
    let uu____411 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____413 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____411, uu____413)  in
  let scopes =
    let uu____424 = let uu____430 = new_scope ()  in [uu____430]  in
    FStar_Util.mk_ref uu____424  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____455 =
        let uu____457 = FStar_ST.read scopes  in
        FStar_Util.find_map uu____457
          (fun uu____474  ->
             match uu____474 with
             | (names1,uu____481) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____455 with
      | None  -> y1
      | Some uu____486 ->
          (FStar_Util.incr ctr;
           (let uu____491 =
              let uu____492 =
                let uu____493 = FStar_ST.read ctr  in
                Prims.string_of_int uu____493  in
              Prims.strcat "__" uu____492  in
            Prims.strcat y1 uu____491))
       in
    let top_scope =
      let uu____498 =
        let uu____503 = FStar_ST.read scopes  in FStar_List.hd uu____503  in
      FStar_All.pipe_left Prims.fst uu____498  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____542 = FStar_Util.incr ctr; FStar_ST.read ctr  in
  let fresh1 pfx =
    let uu____553 =
      let uu____554 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____554  in
    FStar_Util.format2 "%s_%s" pfx uu____553  in
  let string_const s =
    let uu____559 =
      let uu____561 = FStar_ST.read scopes  in
      FStar_Util.find_map uu____561
        (fun uu____578  ->
           match uu____578 with
           | (uu____584,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____559 with
    | Some f -> f
    | None  ->
        let id = next_id1 ()  in
        let f =
          let uu____593 = FStar_SMTEncoding_Util.mk_String_const id  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____593  in
        let top_scope =
          let uu____596 =
            let uu____601 = FStar_ST.read scopes  in FStar_List.hd uu____601
             in
          FStar_All.pipe_left Prims.snd uu____596  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____629 =
    let uu____630 =
      let uu____636 = new_scope ()  in
      let uu____641 = FStar_ST.read scopes  in uu____636 :: uu____641  in
    FStar_ST.write scopes uu____630  in
  let pop1 uu____668 =
    let uu____669 =
      let uu____675 = FStar_ST.read scopes  in FStar_List.tl uu____675  in
    FStar_ST.write scopes uu____669  in
  let mark1 uu____702 = push1 ()  in
  let reset_mark1 uu____706 = pop1 ()  in
  let commit_mark1 uu____710 =
    let uu____711 = FStar_ST.read scopes  in
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
    | uu____771 -> failwith "Impossible"  in
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
let unmangle : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu___136_780 = x  in
    let uu____781 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____781;
      FStar_Syntax_Syntax.index = (uu___136_780.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___136_780.FStar_Syntax_Syntax.sort)
    }
  
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) 
  | Binding_fvar of (FStar_Ident.lident * Prims.string *
  FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term
  Prims.option) 
let uu___is_Binding_var : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____802 -> false
  
let __proj__Binding_var__item___0 :
  binding -> (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let uu___is_Binding_fvar : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____826 -> false
  
let __proj__Binding_fvar__item___0 :
  binding ->
    (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term
      Prims.option * FStar_SMTEncoding_Term.term Prims.option)
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0 
let binder_of_eithervar v1 = (v1, None) 
type env_t =
  {
  bindings: binding Prims.list ;
  depth: Prims.int ;
  tcenv: FStar_TypeChecker_Env.env ;
  warn: Prims.bool ;
  cache:
    (Prims.string * FStar_SMTEncoding_Term.sort Prims.list *
      FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap
    ;
  nolabels: Prims.bool ;
  use_zfuel_name: Prims.bool ;
  encode_non_total_function_typ: Prims.bool }
let print_env : env_t -> Prims.string =
  fun e  ->
    let uu____945 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___112_949  ->
              match uu___112_949 with
              | Binding_var (x,uu____951) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____953,uu____954,uu____955) ->
                  FStar_Syntax_Print.lid_to_string l))
       in
    FStar_All.pipe_right uu____945 (FStar_String.concat ", ")
  
let lookup_binding env f = FStar_Util.find_map env.bindings f 
let caption_t :
  env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option =
  fun env  ->
    fun t  ->
      let uu____988 = FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low
         in
      if uu____988
      then
        let uu____990 = FStar_Syntax_Print.term_to_string t  in
        Some uu____990
      else None
  
let fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string * FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____1001 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____1001)
  
let gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t)
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth)  in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort)
         in
      (ysym, y,
        (let uu___137_1013 = env  in
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
  
let new_term_constant :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t)
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index
         in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
      (ysym, y,
        (let uu___138_1026 = env  in
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
  
let new_term_constant_from_string :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string -> (Prims.string * FStar_SMTEncoding_Term.term * env_t)
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str  in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
        (ysym, y,
          (let uu___139_1042 = env  in
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
  
let push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___140_1052 = env  in
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
  
let lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___113_1068  ->
             match uu___113_1068 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1076 -> None)
         in
      let uu____1079 = aux a  in
      match uu____1079 with
      | None  ->
          let a2 = unmangle a  in
          let uu____1086 = aux a2  in
          (match uu____1086 with
           | None  ->
               let uu____1092 =
                 let uu____1093 = FStar_Syntax_Print.bv_to_string a2  in
                 let uu____1094 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1093 uu____1094
                  in
               failwith uu____1092
           | Some (b,t) -> t)
      | Some (b,t) -> t
  
let new_term_constant_and_tok_from_lid :
  env_t -> FStar_Ident.lident -> (Prims.string * Prims.string * env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x  in
      let ftok = Prims.strcat fname "@tok"  in
      let uu____1114 =
        let uu___141_1115 = env  in
        let uu____1116 =
          let uu____1118 =
            let uu____1119 =
              let uu____1126 =
                let uu____1128 = FStar_SMTEncoding_Util.mkApp (ftok, [])  in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1128  in
              (x, fname, uu____1126, None)  in
            Binding_fvar uu____1119  in
          uu____1118 :: (env.bindings)  in
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
        }  in
      (fname, ftok, uu____1114)
  
let try_lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string * FStar_SMTEncoding_Term.term Prims.option *
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
  
let contains_name : env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1184 =
        lookup_binding env
          (fun uu___115_1186  ->
             match uu___115_1186 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1196 -> None)
         in
      FStar_All.pipe_right uu____1184 FStar_Option.isSome
  
let lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string * FStar_SMTEncoding_Term.term Prims.option *
        FStar_SMTEncoding_Term.term Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1209 = try_lookup_lid env a  in
      match uu____1209 with
      | None  ->
          let uu____1226 =
            let uu____1227 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____1227  in
          failwith uu____1226
      | Some s -> s
  
let push_free_var :
  env_t ->
    FStar_Ident.lident ->
      Prims.string -> FStar_SMTEncoding_Term.term Prims.option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___142_1258 = env  in
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
  
let push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1270 = lookup_lid env x  in
        match uu____1270 with
        | (t1,t2,uu____1278) ->
            let t3 =
              let uu____1284 =
                let uu____1288 =
                  let uu____1290 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])
                     in
                  [uu____1290]  in
                (f, uu____1288)  in
              FStar_SMTEncoding_Util.mkApp uu____1284  in
            let uu___143_1293 = env  in
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
  
let try_lookup_free_var :
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1303 = try_lookup_lid env l  in
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
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____1340 Prims.fst  in
                           FStar_Util.starts_with uu____1339 "fuel"  in
                         if uu____1338
                         then
                           let uu____1342 =
                             let uu____1343 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1343
                               fuel
                              in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1342
                         else Some t
                     | uu____1346 -> Some t)
                | uu____1347 -> None))
  
let lookup_free_var env a =
  let uu____1365 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
  match uu____1365 with
  | Some t -> t
  | None  ->
      let uu____1368 =
        let uu____1369 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
        FStar_Util.format1 "Name not found: %s" uu____1369  in
      failwith uu____1368
  
let lookup_free_var_name env a =
  let uu____1386 = lookup_lid env a.FStar_Syntax_Syntax.v  in
  match uu____1386 with | (x,uu____1393,uu____1394) -> x 
let lookup_free_var_sym env a =
  let uu____1418 = lookup_lid env a.FStar_Syntax_Syntax.v  in
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
  
let tok_of_name :
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
        FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
      let uu____1517 = FStar_Options.unthrottle_inductives ()  in
      if uu____1517
      then fallback ()
      else
        (let uu____1519 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
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
                       | uu____1538 -> p))
                in
             let pats1 = FStar_List.map add_fuel1 pats  in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1552 = add_fuel1 guards  in
                         FStar_SMTEncoding_Util.mk_and_l uu____1552
                     | uu____1554 ->
                         let uu____1555 = add_fuel1 [guard]  in
                         FStar_All.pipe_right uu____1555 FStar_List.hd
                      in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1558 -> body  in
             let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars  in
             FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
  
let mkForall_fuel :
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
    FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = mkForall_fuel' (Prims.parse_int "1") 
let head_normal : env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
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
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____1602 FStar_Option.isNone
      | uu____1615 -> false
  
let head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1622 =
        let uu____1623 = FStar_Syntax_Util.un_uinst t  in
        uu____1623.FStar_Syntax_Syntax.n  in
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
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____1686 FStar_Option.isSome
      | uu____1699 -> false
  
let whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1706 = head_normal env t  in
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
  
let norm : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
  
let trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____1717 =
      let uu____1721 = FStar_Syntax_Syntax.null_binder t  in [uu____1721]  in
    let uu____1722 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None
       in
    FStar_Syntax_Util.abs uu____1717 uu____1722 None
  
let mk_Apply :
  FStar_SMTEncoding_Term.term ->
    (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list ->
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
                    let uu____1749 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1749
                | s ->
                    let uu____1752 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1752) e)
  
let mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let is_app : FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___118_1764  ->
    match uu___118_1764 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1765 -> false
  
let is_eta :
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
                          | uu____1823 -> false) args vars)
                 in
              if uu____1813 then tok_of_name env f else None
          | (uu____1826,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t1  in
              let uu____1829 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1831 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____1831))
                 in
              if uu____1829 then Some t1 else None
          | uu____1834 -> None  in
        aux t (FStar_List.rev vars)
  
let reify_body :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let tm = FStar_Syntax_Util.mk_reify t  in
      let tm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Reify;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm
         in
      (let uu____1849 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____1849
       then
         let uu____1850 = FStar_Syntax_Print.term_to_string tm  in
         let uu____1851 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____1850 uu____1851
       else ());
      tm'
  
type label = (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)
type labels = label Prims.list
type pattern =
  {
  pat_vars: (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list ;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
    ;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term ;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list
    }
exception Let_rec_unencodeable 
let uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____1933 -> false
  
let encode_const : FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
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
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c)
                 in
              FStar_SMTEncoding_Term.boxInt uu____1945  in
            [uu____1944]  in
          ("FStar.Char.Char", uu____1942)  in
        FStar_SMTEncoding_Util.mkApp uu____1938
    | FStar_Const.Const_int (i,None ) ->
        let uu____1953 = FStar_SMTEncoding_Util.mkInteger i  in
        FStar_SMTEncoding_Term.boxInt uu____1953
    | FStar_Const.Const_int (i,Some uu____1955) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____1964) ->
        let uu____1967 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes
           in
        varops.string_const uu____1967
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____1971 =
          let uu____1972 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "Unhandled constant: %s" uu____1972  in
        failwith uu____1971
  
let as_function_typ :
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t  in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____1991 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1999 ->
            let uu____2004 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____2004
        | uu____2005 ->
            if norm1
            then let uu____2006 = whnf env t1  in aux false uu____2006
            else
              (let uu____2008 =
                 let uu____2009 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____2010 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2009 uu____2010
                  in
               failwith uu____2008)
         in
      aux true t0
  
let curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | uu____2031 ->
        let uu____2032 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____2032)
  
let rec encode_binders :
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term
          Prims.list * env_t * FStar_SMTEncoding_Term.decls_t *
          FStar_Syntax_Syntax.bv Prims.list)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____2175 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____2175
         then
           let uu____2176 = FStar_Syntax_Print.binders_to_string ", " bs  in
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
                           let x = unmangle (Prims.fst b)  in
                           let uu____2266 = gen_term_var env1 x  in
                           match uu____2266 with
                           | (xxsym,xx,env') ->
                               let uu____2280 =
                                 let uu____2283 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2283 env1 xx
                                  in
                               (match uu____2280 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____2257 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____2178 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))

and encode_term_pred :
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2371 = encode_term t env  in
          match uu____2371 with
          | (t1,decls) ->
              let uu____2378 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2378, decls)

and encode_term_pred' :
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2386 = encode_term t env  in
          match uu____2386 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2395 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2395, decls)
               | Some f ->
                   let uu____2397 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2397, decls))

and encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____2404 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____2404
       then
         let uu____2405 = FStar_Syntax_Print.tag_of_term t  in
         let uu____2406 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____2407 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2405 uu____2406
           uu____2407
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2412 =
             let uu____2413 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____2414 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____2415 = FStar_Syntax_Print.term_to_string t0  in
             let uu____2416 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2413
               uu____2414 uu____2415 uu____2416
              in
           failwith uu____2412
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2420 =
             let uu____2421 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2421
              in
           failwith uu____2420
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2426) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2456) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2465 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____2465, [])
       | FStar_Syntax_Syntax.Tm_type uu____2471 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2474) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2480 = encode_const c  in (uu____2480, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let uu____2494 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____2494 with
            | (binders1,res) ->
                let uu____2501 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____2501
                then
                  let uu____2504 = encode_binders None binders1 env  in
                  (match uu____2504 with
                   | (vars,guards,env',decls,uu____2519) ->
                       let fsym =
                         let uu____2529 = varops.fresh "f"  in
                         (uu____2529, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____2532 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___144_2536 = env.tcenv  in
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
                            }) res
                          in
                       (match uu____2532 with
                        | (pre_opt,res_t) ->
                            let uu____2543 =
                              encode_term_pred None res_t env' app  in
                            (match uu____2543 with
                             | (res_pred,decls') ->
                                 let uu____2550 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2557 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____2557, [])
                                   | Some pre ->
                                       let uu____2560 =
                                         encode_formula pre env'  in
                                       (match uu____2560 with
                                        | (guard,decls0) ->
                                            let uu____2568 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____2568, decls0))
                                    in
                                 (match uu____2550 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2576 =
                                          let uu____2582 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____2582)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2576
                                         in
                                      let cvars =
                                        let uu____2592 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____2592
                                          (FStar_List.filter
                                             (fun uu____2598  ->
                                                match uu____2598 with
                                                | (x,uu____2602) ->
                                                    x <> (Prims.fst fsym)))
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____2613 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____2613 with
                                       | Some (t',sorts,uu____2629) ->
                                           let uu____2639 =
                                             let uu____2640 =
                                               let uu____2644 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               (t', uu____2644)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2640
                                              in
                                           (uu____2639, [])
                                       | None  ->
                                           let tsym =
                                             let uu____2660 =
                                               let uu____2661 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2661
                                                in
                                             varops.mk_unique uu____2660  in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars
                                              in
                                           let caption =
                                             let uu____2668 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____2668
                                             then
                                               let uu____2670 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               Some uu____2670
                                             else None  in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption)
                                              in
                                           let t1 =
                                             let uu____2676 =
                                               let uu____2680 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____2680)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2676
                                              in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type
                                              in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym
                                                in
                                             let uu____2688 =
                                               let uu____2692 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____2692, (Some a_name),
                                                 a_name)
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2688
                                              in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1
                                              in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1
                                              in
                                           let pre_typing =
                                             let a_name =
                                               Prims.strcat "pre_typing_"
                                                 tsym
                                                in
                                             let uu____2705 =
                                               let uu____2709 =
                                                 let uu____2710 =
                                                   let uu____2716 =
                                                     let uu____2717 =
                                                       let uu____2720 =
                                                         let uu____2721 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2721
                                                          in
                                                       (f_has_t, uu____2720)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2717
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2716)
                                                    in
                                                 mkForall_fuel uu____2710  in
                                               (uu____2709,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 a_name)
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2705
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____2734 =
                                               let uu____2738 =
                                                 let uu____2739 =
                                                   let uu____2745 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2745)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2739
                                                  in
                                               (uu____2738, (Some a_name),
                                                 a_name)
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2734
                                              in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1]))
                                              in
                                           (FStar_Util.smap_add env.cache
                                              tkey_hash
                                              (tsym, cvar_sorts, t_decls);
                                            (t1, t_decls)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow"  in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort, None)
                      in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, [])  in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym  in
                     let uu____2776 =
                       let uu____2780 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____2780, (Some "Typing for non-total arrows"),
                         a_name)
                        in
                     FStar_SMTEncoding_Term.Assume uu____2776  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____2789 =
                       let uu____2793 =
                         let uu____2794 =
                           let uu____2800 =
                             let uu____2801 =
                               let uu____2804 =
                                 let uu____2805 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2805
                                  in
                               (f_has_t, uu____2804)  in
                             FStar_SMTEncoding_Util.mkImp uu____2801  in
                           ([[f_has_t]], [fsym], uu____2800)  in
                         mkForall_fuel uu____2794  in
                       (uu____2793, (Some a_name), a_name)  in
                     FStar_SMTEncoding_Term.Assume uu____2789  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2819 ->
           let uu____2824 =
             let uu____2827 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____2827 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2832;
                 FStar_Syntax_Syntax.pos = uu____2833;
                 FStar_Syntax_Syntax.vars = uu____2834;_} ->
                 let uu____2841 = FStar_Syntax_Subst.open_term [(x, None)] f
                    in
                 (match uu____2841 with
                  | (b,f1) ->
                      let uu____2855 =
                        let uu____2856 = FStar_List.hd b  in
                        Prims.fst uu____2856  in
                      (uu____2855, f1))
             | uu____2861 -> failwith "impossible"  in
           (match uu____2824 with
            | (x,f) ->
                let uu____2868 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____2868 with
                 | (base_t,decls) ->
                     let uu____2875 = gen_term_var env x  in
                     (match uu____2875 with
                      | (x1,xtm,env') ->
                          let uu____2884 = encode_formula f env'  in
                          (match uu____2884 with
                           | (refinement,decls') ->
                               let uu____2891 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____2891 with
                                | (fsym,fterm) ->
                                    let encoding =
                                      let uu____2899 =
                                        let uu____2902 =
                                          FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                            (Some fterm) xtm base_t
                                           in
                                        (uu____2902, refinement)  in
                                      FStar_SMTEncoding_Util.mkAnd uu____2899
                                       in
                                    let cvars =
                                      let uu____2907 =
                                        FStar_SMTEncoding_Term.free_variables
                                          encoding
                                         in
                                      FStar_All.pipe_right uu____2907
                                        (FStar_List.filter
                                           (fun uu____2913  ->
                                              match uu____2913 with
                                              | (y,uu____2917) ->
                                                  (y <> x1) && (y <> fsym)))
                                       in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort)
                                       in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars), encoding)
                                       in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey
                                       in
                                    let uu____2936 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____2936 with
                                     | Some (t1,uu____2951,uu____2952) ->
                                         let uu____2962 =
                                           let uu____2963 =
                                             let uu____2967 =
                                               FStar_All.pipe_right cvars
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             (t1, uu____2967)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2963
                                            in
                                         (uu____2962, [])
                                     | None  ->
                                         let tsym =
                                           let uu____2983 =
                                             let uu____2984 =
                                               FStar_Util.digest_of_string
                                                 tkey_hash
                                                in
                                             Prims.strcat "Tm_refine_"
                                               uu____2984
                                              in
                                           varops.mk_unique uu____2983  in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars  in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None)
                                            in
                                         let t1 =
                                           let uu____2993 =
                                             let uu____2997 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars
                                                in
                                             (tsym, uu____2997)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2993
                                            in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (Some fterm) xtm t1
                                            in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t1
                                             FStar_SMTEncoding_Term.mk_Term_type
                                            in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t
                                            in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t1
                                            in
                                         let t_haseq1 =
                                           let uu____3007 =
                                             let uu____3011 =
                                               let uu____3012 =
                                                 let uu____3018 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars,
                                                   uu____3018)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3012
                                                in
                                             (uu____3011,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3007
                                            in
                                         let t_kinding =
                                           let uu____3028 =
                                             let uu____3032 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars,
                                                   t_has_kind)
                                                in
                                             (uu____3032,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3028
                                            in
                                         let t_interp =
                                           let uu____3042 =
                                             let uu____3046 =
                                               let uu____3047 =
                                                 let uu____3053 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars), uu____3053)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3047
                                                in
                                             let uu____3065 =
                                               let uu____3067 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               Some uu____3067  in
                                             (uu____3046, uu____3065,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3042
                                            in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         (FStar_Util.smap_add env.cache
                                            tkey_hash
                                            (tsym, cvar_sorts, t_decls);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3095 = FStar_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3095  in
           let uu____3099 = encode_term_pred None k env ttm  in
           (match uu____3099 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3107 =
                    let uu____3111 =
                      let uu____3112 =
                        let uu____3113 =
                          let uu____3114 = FStar_Unionfind.uvar_id uv  in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3114
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____3113  in
                      varops.mk_unique uu____3112  in
                    (t_has_k, (Some "Uvar typing"), uu____3111)  in
                  FStar_SMTEncoding_Term.Assume uu____3107  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3120 ->
           let uu____3130 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____3130 with
            | (head1,args_e) ->
                let uu____3158 =
                  let uu____3166 =
                    let uu____3167 = FStar_Syntax_Subst.compress head1  in
                    uu____3167.FStar_Syntax_Syntax.n  in
                  (uu____3166, args_e)  in
                (match uu____3158 with
                 | (uu____3177,uu____3178) when head_redex env head1 ->
                     let uu____3189 = whnf env t  in
                     encode_term uu____3189 env
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
                     let uu____3263 = encode_term v1 env  in
                     (match uu____3263 with
                      | (v11,decls1) ->
                          let uu____3270 = encode_term v2 env  in
                          (match uu____3270 with
                           | (v21,decls2) ->
                               let uu____3277 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____3277,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3279) ->
                     let e0 =
                       let uu____3293 =
                         let uu____3296 =
                           let uu____3297 =
                             let uu____3307 =
                               let uu____3313 = FStar_List.hd args_e  in
                               [uu____3313]  in
                             (head1, uu____3307)  in
                           FStar_Syntax_Syntax.Tm_app uu____3297  in
                         FStar_Syntax_Syntax.mk uu____3296  in
                       uu____3293 None head1.FStar_Syntax_Syntax.pos  in
                     ((let uu____3346 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____3346
                       then
                         let uu____3347 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Trying to normalize %s\n"
                           uu____3347
                       else ());
                      (let e01 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Reify;
                           FStar_TypeChecker_Normalize.Eager_unfolding;
                           FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                           env.tcenv e0
                          in
                       (let uu____3351 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify")
                           in
                        if uu____3351
                        then
                          let uu____3352 =
                            FStar_Syntax_Print.term_to_string e01  in
                          FStar_Util.print1 "Result of normalization %s\n"
                            uu____3352
                        else ());
                       (let e02 =
                          let uu____3355 =
                            let uu____3356 =
                              let uu____3357 =
                                FStar_Syntax_Subst.compress e01  in
                              uu____3357.FStar_Syntax_Syntax.n  in
                            match uu____3356 with
                            | FStar_Syntax_Syntax.Tm_app uu____3360 -> false
                            | uu____3370 -> true  in
                          if uu____3355
                          then e01
                          else
                            (let uu____3372 =
                               FStar_Syntax_Util.head_and_args e01  in
                             match uu____3372 with
                             | (head2,args) ->
                                 let uu____3398 =
                                   let uu____3399 =
                                     let uu____3400 =
                                       FStar_Syntax_Subst.compress head2  in
                                     uu____3400.FStar_Syntax_Syntax.n  in
                                   match uu____3399 with
                                   | FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_reify ) -> true
                                   | uu____3403 -> false  in
                                 if uu____3398
                                 then
                                   (match args with
                                    | x::[] -> Prims.fst x
                                    | uu____3419 ->
                                        failwith
                                          "Impossible : Reify applied to multiple arguments after normalization.")
                                 else e01)
                           in
                        let e =
                          match args_e with
                          | uu____3427::[] -> e02
                          | uu____3440 ->
                              let uu____3446 =
                                let uu____3449 =
                                  let uu____3450 =
                                    let uu____3460 = FStar_List.tl args_e  in
                                    (e02, uu____3460)  in
                                  FStar_Syntax_Syntax.Tm_app uu____3450  in
                                FStar_Syntax_Syntax.mk uu____3449  in
                              uu____3446 None t0.FStar_Syntax_Syntax.pos
                           in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3483),(arg,uu____3485)::[]) -> encode_term arg env
                 | uu____3503 ->
                     let uu____3511 = encode_args args_e env  in
                     (match uu____3511 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3544 = encode_term head1 env  in
                            match uu____3544 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3583 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____3583 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3625  ->
                                                 fun uu____3626  ->
                                                   match (uu____3625,
                                                           uu____3626)
                                                   with
                                                   | ((bv,uu____3640),
                                                      (a,uu____3642)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____3656 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____3656
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____3661 =
                                            encode_term_pred None ty env
                                              app_tm
                                             in
                                          (match uu____3661 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____3671 =
                                                   let uu____3675 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____3680 =
                                                     let uu____3681 =
                                                       let uu____3682 =
                                                         let uu____3683 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____3683
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3682
                                                        in
                                                     varops.mk_unique
                                                       uu____3681
                                                      in
                                                   (uu____3675,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3680)
                                                    in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3671
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____3700 = lookup_free_var_sym env fv  in
                            match uu____3700 with
                            | (fname,fuel_args) ->
                                let tm =
                                  FStar_SMTEncoding_Util.mkApp'
                                    (fname,
                                      (FStar_List.append fuel_args args))
                                   in
                                (tm, decls)
                             in
                          let head2 = FStar_Syntax_Subst.compress head1  in
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
                                let uu____3738 =
                                  let uu____3739 =
                                    let uu____3742 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____3742 Prims.fst
                                     in
                                  FStar_All.pipe_right uu____3739 Prims.snd
                                   in
                                Some uu____3738
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3761,(FStar_Util.Inl t1,uu____3763),uu____3764)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3802,(FStar_Util.Inr c,uu____3804),uu____3805)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3843 -> None  in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3863 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3863
                                  in
                               let uu____3864 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____3864 with
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
                                     | uu____3889 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3934 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____3934 with
            | (bs1,body1,opening) ->
                let fallback uu____3949 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding"))
                     in
                  let uu____3954 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____3954, [decl])  in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3965 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1  in
                      Prims.op_Negation uu____3965
                  | FStar_Util.Inr (eff,uu____3967) ->
                      let uu____3973 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff
                         in
                      FStar_All.pipe_right uu____3973 Prims.op_Negation
                   in
                let reify_comp_and_body env1 c body2 =
                  let reified_body = reify_body env1.tcenv body2  in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4018 = lc.FStar_Syntax_Syntax.comp ()  in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___145_4019 = env1.tcenv  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___145_4019.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___145_4019.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___145_4019.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___145_4019.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___145_4019.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___145_4019.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___145_4019.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___145_4019.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___145_4019.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___145_4019.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___145_4019.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___145_4019.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___145_4019.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___145_4019.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___145_4019.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___145_4019.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___145_4019.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___145_4019.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___145_4019.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___145_4019.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___145_4019.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___145_4019.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___145_4019.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4018 FStar_Syntax_Syntax.U_unknown
                           in
                        let uu____4020 =
                          let uu____4021 = FStar_Syntax_Syntax.mk_Total typ
                             in
                          FStar_Syntax_Util.lcomp_of_comp uu____4021  in
                        FStar_Util.Inl uu____4020
                    | FStar_Util.Inr (eff_name,uu____4028) -> c  in
                  (c1, reified_body)  in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4059 =
                        let uu____4060 = lc1.FStar_Syntax_Syntax.comp ()  in
                        FStar_Syntax_Subst.subst_comp opening uu____4060  in
                      FStar_All.pipe_right uu____4059
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4072 =
                        let uu____4073 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____4073 Prims.fst  in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4081 =
                          let uu____4082 = new_uvar1 ()  in
                          FStar_Syntax_Syntax.mk_Total uu____4082  in
                        FStar_All.pipe_right uu____4081
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4086 =
                             let uu____4087 = new_uvar1 ()  in
                             FStar_Syntax_Syntax.mk_GTotal uu____4087  in
                           FStar_All.pipe_right uu____4086
                             (fun _0_33  -> Some _0_33))
                        else None
                   in
                (match lopt with
                 | None  ->
                     ((let uu____4098 =
                         let uu____4099 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4099
                          in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4098);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc  in
                     let uu____4114 =
                       (is_impure lc1) &&
                         (let uu____4115 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1
                             in
                          Prims.op_Negation uu____4115)
                        in
                     if uu____4114
                     then fallback ()
                     else
                       (let uu____4119 = encode_binders None bs1 env  in
                        match uu____4119 with
                        | (vars,guards,envbody,decls,uu____4134) ->
                            let uu____4141 =
                              let uu____4149 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1
                                 in
                              if uu____4149
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1)  in
                            (match uu____4141 with
                             | (lc2,body2) ->
                                 let uu____4174 = encode_term body2 envbody
                                    in
                                 (match uu____4174 with
                                  | (body3,decls') ->
                                      let key_body =
                                        let uu____4182 =
                                          let uu____4188 =
                                            let uu____4189 =
                                              let uu____4192 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____4192, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____4189
                                             in
                                          ([], vars, uu____4188)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4182
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____4203 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____4203 with
                                       | Some (t1,uu____4218,uu____4219) ->
                                           let uu____4229 =
                                             let uu____4230 =
                                               let uu____4234 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (t1, uu____4234)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4230
                                              in
                                           (uu____4229, [])
                                       | None  ->
                                           let uu____4245 =
                                             is_eta env vars body3  in
                                           (match uu____4245 with
                                            | Some t1 -> (t1, [])
                                            | None  ->
                                                let cvar_sorts =
                                                  FStar_List.map Prims.snd
                                                    cvars
                                                   in
                                                let fsym =
                                                  let uu____4256 =
                                                    let uu____4257 =
                                                      FStar_Util.digest_of_string
                                                        tkey_hash
                                                       in
                                                    Prims.strcat "Tm_abs_"
                                                      uu____4257
                                                     in
                                                  varops.mk_unique uu____4256
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      None)
                                                   in
                                                let f =
                                                  let uu____4262 =
                                                    let uu____4266 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars
                                                       in
                                                    (fsym, uu____4266)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4262
                                                   in
                                                let app = mk_Apply f vars  in
                                                let typing_f =
                                                  let uu____4274 =
                                                    codomain_eff lc2  in
                                                  match uu____4274 with
                                                  | None  -> []
                                                  | Some c ->
                                                      let tfun =
                                                        FStar_Syntax_Util.arrow
                                                          bs1 c
                                                         in
                                                      let uu____4281 =
                                                        encode_term_pred None
                                                          tfun env f
                                                         in
                                                      (match uu____4281 with
                                                       | (f_has_t,decls'') ->
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym
                                                              in
                                                           let uu____4288 =
                                                             let uu____4290 =
                                                               let uu____4291
                                                                 =
                                                                 let uu____4295
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkForall
                                                                    ([[f]],
                                                                    cvars,
                                                                    f_has_t)
                                                                    in
                                                                 (uu____4295,
                                                                   (Some
                                                                    a_name),
                                                                   a_name)
                                                                  in
                                                               FStar_SMTEncoding_Term.Assume
                                                                 uu____4291
                                                                in
                                                             [uu____4290]  in
                                                           FStar_List.append
                                                             decls''
                                                             uu____4288)
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____4303 =
                                                    let uu____4307 =
                                                      let uu____4308 =
                                                        let uu____4314 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars),
                                                          uu____4314)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____4308
                                                       in
                                                    (uu____4307,
                                                      (Some a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Term.Assume
                                                    uu____4303
                                                   in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          (fdecl :: typing_f)
                                                          [interp_f]))
                                                   in
                                                (FStar_Util.smap_add
                                                   env.cache tkey_hash
                                                   (fsym, cvar_sorts,
                                                     f_decls);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4332,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4333;
                          FStar_Syntax_Syntax.lbunivs = uu____4334;
                          FStar_Syntax_Syntax.lbtyp = uu____4335;
                          FStar_Syntax_Syntax.lbeff = uu____4336;
                          FStar_Syntax_Syntax.lbdef = uu____4337;_}::uu____4338),uu____4339)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4357;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4359;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4375 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec"  in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None)
                in
             let uu____4388 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort)
                in
             (uu____4388, [decl_e])))
       | FStar_Syntax_Syntax.Tm_match (e,pats) ->
           encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
             encode_term)

and encode_let :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          env_t ->
            (FStar_Syntax_Syntax.term ->
               env_t ->
                 (FStar_SMTEncoding_Term.term *
                   FStar_SMTEncoding_Term.decls_t))
              ->
              (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____4430 = encode_term e1 env  in
              match uu____4430 with
              | (ee1,decls1) ->
                  let uu____4437 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2  in
                  (match uu____4437 with
                   | (xs,e21) ->
                       let uu____4451 = FStar_List.hd xs  in
                       (match uu____4451 with
                        | (x1,uu____4459) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____4461 = encode_body e21 env'  in
                            (match uu____4461 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))

and encode_match :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        env_t ->
          (FStar_Syntax_Syntax.term ->
             env_t ->
               (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
            -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____4483 =
              let uu____4487 =
                let uu____4488 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____4488  in
              gen_term_var env uu____4487  in
            match uu____4483 with
            | (scrsym,scr',env1) ->
                let uu____4502 = encode_term e env1  in
                (match uu____4502 with
                 | (scr,decls) ->
                     let uu____4509 =
                       let encode_branch b uu____4525 =
                         match uu____4525 with
                         | (else_case,decls1) ->
                             let uu____4536 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____4536 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p  in
                                  FStar_List.fold_right
                                    (fun uu____4566  ->
                                       fun uu____4567  ->
                                         match (uu____4566, uu____4567) with
                                         | ((env0,pattern),(else_case1,decls2))
                                             ->
                                             let guard = pattern.guard scr'
                                                in
                                             let projections =
                                               pattern.projections scr'  in
                                             let env2 =
                                               FStar_All.pipe_right
                                                 projections
                                                 (FStar_List.fold_left
                                                    (fun env2  ->
                                                       fun uu____4604  ->
                                                         match uu____4604
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1)
                                                in
                                             let uu____4609 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4624 =
                                                     encode_term w1 env2  in
                                                   (match uu____4624 with
                                                    | (w2,decls21) ->
                                                        let uu____4632 =
                                                          let uu____4633 =
                                                            let uu____4636 =
                                                              let uu____4637
                                                                =
                                                                let uu____4640
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue
                                                                   in
                                                                (w2,
                                                                  uu____4640)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4637
                                                               in
                                                            (guard,
                                                              uu____4636)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4633
                                                           in
                                                        (uu____4632, decls21))
                                                in
                                             (match uu____4609 with
                                              | (guard1,decls21) ->
                                                  let uu____4648 =
                                                    encode_br br env2  in
                                                  (match uu____4648 with
                                                   | (br1,decls3) ->
                                                       let uu____4656 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1)
                                                          in
                                                       (uu____4656,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____4509 with
                      | (match_tm,decls1) ->
                          let uu____4668 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____4668, decls1)))

and encode_pat :
  env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4699 ->
          let uu____4700 = encode_one_pat env pat  in [uu____4700]

and encode_one_pat : env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4712 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____4712
       then
         let uu____4713 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4713
       else ());
      (let uu____4715 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____4715 with
       | (vars,pat_term) ->
           let uu____4725 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4748  ->
                     fun v1  ->
                       match uu____4748 with
                       | (env1,vars1) ->
                           let uu____4776 = gen_term_var env1 v1  in
                           (match uu____4776 with
                            | (xx,uu____4788,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____4725 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4835 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4843 =
                        let uu____4846 = encode_const c  in
                        (scrutinee, uu____4846)  in
                      FStar_SMTEncoding_Util.mkEq uu____4843
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____4865 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____4865 with
                        | (uu____4869,uu____4870::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4872 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4893  ->
                                  match uu____4893 with
                                  | (arg,uu____4899) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____4909 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____4909))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4928 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4943 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4958 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4980  ->
                                  match uu____4980 with
                                  | (arg,uu____4989) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____4999 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____4999))
                         in
                      FStar_All.pipe_right uu____4958 FStar_List.flatten
                   in
                let pat_term1 uu____5015 = encode_term pat_term env1  in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  }  in
                (env1, pattern)))

and encode_args :
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list *
        FStar_SMTEncoding_Term.decls_t)
  =
  fun l  ->
    fun env  ->
      let uu____5022 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5037  ->
                fun uu____5038  ->
                  match (uu____5037, uu____5038) with
                  | ((tms,decls),(t,uu____5058)) ->
                      let uu____5069 = encode_term t env  in
                      (match uu____5069 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____5022 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and encode_function_type_as_formula :
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.term Prims.option ->
      FStar_Syntax_Syntax.typ ->
        env_t ->
          (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun induction_on  ->
    fun new_pats  ->
      fun t  ->
        fun env  ->
          let list_elements1 e =
            let uu____5107 = FStar_Syntax_Util.list_elements e  in
            match uu____5107 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 [])
             in
          let one_pat p =
            let uu____5125 =
              let uu____5135 = FStar_Syntax_Util.unmeta p  in
              FStar_All.pipe_right uu____5135 FStar_Syntax_Util.head_and_args
               in
            match uu____5125 with
            | (head1,args) ->
                let uu____5166 =
                  let uu____5174 =
                    let uu____5175 = FStar_Syntax_Util.un_uinst head1  in
                    uu____5175.FStar_Syntax_Syntax.n  in
                  (uu____5174, args)  in
                (match uu____5166 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5189,uu____5190)::(e,uu____5192)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5223)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5244 -> failwith "Unexpected pattern term")
             in
          let lemma_pats p =
            let elts = list_elements1 p  in
            let smt_pat_or t1 =
              let uu____5277 =
                let uu____5287 = FStar_Syntax_Util.unmeta t1  in
                FStar_All.pipe_right uu____5287
                  FStar_Syntax_Util.head_and_args
                 in
              match uu____5277 with
              | (head1,args) ->
                  let uu____5316 =
                    let uu____5324 =
                      let uu____5325 = FStar_Syntax_Util.un_uinst head1  in
                      uu____5325.FStar_Syntax_Syntax.n  in
                    (uu____5324, args)  in
                  (match uu____5316 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5338)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5358 -> None)
               in
            match elts with
            | t1::[] ->
                let uu____5376 = smt_pat_or t1  in
                (match uu____5376 with
                 | Some e ->
                     let uu____5392 = list_elements1 e  in
                     FStar_All.pipe_right uu____5392
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5409 = list_elements1 branch1  in
                             FStar_All.pipe_right uu____5409
                               (FStar_List.map one_pat)))
                 | uu____5423 ->
                     let uu____5427 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                     [uu____5427])
            | uu____5458 ->
                let uu____5460 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                [uu____5460]
             in
          let uu____5491 =
            let uu____5507 =
              let uu____5508 = FStar_Syntax_Subst.compress t  in
              uu____5508.FStar_Syntax_Syntax.n  in
            match uu____5507 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5538 = FStar_Syntax_Subst.open_comp binders c  in
                (match uu____5538 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5573;
                            FStar_Syntax_Syntax.effect_name = uu____5574;
                            FStar_Syntax_Syntax.result_typ = uu____5575;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5577)::(post,uu____5579)::(pats,uu____5581)::[];
                            FStar_Syntax_Syntax.flags = uu____5582;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats  in
                          let uu____5616 = lemma_pats pats'  in
                          (binders1, pre, post, uu____5616)
                      | uu____5635 -> failwith "impos"))
            | uu____5651 -> failwith "Impos"  in
          match uu____5491 with
          | (binders,pre,post,patterns) ->
              let uu____5695 = encode_binders None binders env  in
              (match uu____5695 with
               | (vars,guards,env1,decls,uu____5710) ->
                   let uu____5717 =
                     let uu____5724 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5755 =
                                 let uu____5760 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5776  ->
                                           match uu____5776 with
                                           | (t1,uu____5783) ->
                                               encode_term t1
                                                 (let uu___146_5786 = env1
                                                     in
                                                  {
                                                    bindings =
                                                      (uu___146_5786.bindings);
                                                    depth =
                                                      (uu___146_5786.depth);
                                                    tcenv =
                                                      (uu___146_5786.tcenv);
                                                    warn =
                                                      (uu___146_5786.warn);
                                                    cache =
                                                      (uu___146_5786.cache);
                                                    nolabels =
                                                      (uu___146_5786.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___146_5786.encode_non_total_function_typ)
                                                  })))
                                    in
                                 FStar_All.pipe_right uu____5760
                                   FStar_List.unzip
                                  in
                               match uu____5755 with
                               | (pats,decls1) -> (pats, decls1)))
                        in
                     FStar_All.pipe_right uu____5724 FStar_List.unzip  in
                   (match uu____5717 with
                    | (pats,decls') ->
                        let decls'1 = FStar_List.flatten decls'  in
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
                                           let uu____5850 =
                                             let uu____5851 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l
                                                in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5851 e
                                              in
                                           uu____5850 :: p))
                               | uu____5852 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5881 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e
                                                    in
                                                 uu____5881 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5889 =
                                           let uu____5890 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort)
                                              in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5890 tl1
                                            in
                                         aux uu____5889 vars2
                                     | uu____5891 -> pats  in
                                   let uu____5895 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   aux uu____5895 vars)
                           in
                        let env2 =
                          let uu___147_5897 = env1  in
                          {
                            bindings = (uu___147_5897.bindings);
                            depth = (uu___147_5897.depth);
                            tcenv = (uu___147_5897.tcenv);
                            warn = (uu___147_5897.warn);
                            cache = (uu___147_5897.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___147_5897.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___147_5897.encode_non_total_function_typ)
                          }  in
                        let uu____5898 =
                          let uu____5901 = FStar_Syntax_Util.unmeta pre  in
                          encode_formula uu____5901 env2  in
                        (match uu____5898 with
                         | (pre1,decls'') ->
                             let uu____5906 =
                               let uu____5909 = FStar_Syntax_Util.unmeta post
                                  in
                               encode_formula uu____5909 env2  in
                             (match uu____5906 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls'''))
                                     in
                                  let uu____5916 =
                                    let uu____5917 =
                                      let uu____5923 =
                                        let uu____5924 =
                                          let uu____5927 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards)
                                             in
                                          (uu____5927, post1)  in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5924
                                         in
                                      (pats1, vars, uu____5923)  in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5917
                                     in
                                  (uu____5916, decls1)))))

and encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5940 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____5940
        then
          let uu____5941 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____5942 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5941 uu____5942
        else ()  in
      let enc f r l =
        let uu____5969 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5982 = encode_term (Prims.fst x) env  in
                 match uu____5982 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____5969 with
        | (decls,args) ->
            let uu____5999 =
              let uu___148_6000 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___148_6000.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___148_6000.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____5999, decls)
         in
      let const_op f r uu____6019 = let uu____6022 = f r  in (uu____6022, [])
         in
      let un_op f l =
        let uu____6038 = FStar_List.hd l  in FStar_All.pipe_left f uu____6038
         in
      let bin_op f uu___120_6051 =
        match uu___120_6051 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6059 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____6086 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6095  ->
                 match uu____6095 with
                 | (t,uu____6103) ->
                     let uu____6104 = encode_formula t env  in
                     (match uu____6104 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____6086 with
        | (decls,phis) ->
            let uu____6121 =
              let uu___149_6122 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___149_6122.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___149_6122.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____6121, decls)
         in
      let eq_op r uu___121_6138 =
        match uu___121_6138 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6198 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
            uu____6198 r [e1; e2]
        | l ->
            let uu____6218 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
            uu____6218 r l
         in
      let mk_imp1 r uu___122_6237 =
        match uu___122_6237 with
        | (lhs,uu____6241)::(rhs,uu____6243)::[] ->
            let uu____6264 = encode_formula rhs env  in
            (match uu____6264 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6273) ->
                      (l1, decls1)
                  | uu____6276 ->
                      let uu____6277 = encode_formula lhs env  in
                      (match uu____6277 with
                       | (l2,decls2) ->
                           let uu____6284 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____6284, (FStar_List.append decls1 decls2)))))
        | uu____6286 -> failwith "impossible"  in
      let mk_ite r uu___123_6301 =
        match uu___123_6301 with
        | (guard,uu____6305)::(_then,uu____6307)::(_else,uu____6309)::[] ->
            let uu____6338 = encode_formula guard env  in
            (match uu____6338 with
             | (g,decls1) ->
                 let uu____6345 = encode_formula _then env  in
                 (match uu____6345 with
                  | (t,decls2) ->
                      let uu____6352 = encode_formula _else env  in
                      (match uu____6352 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6361 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____6380 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l  in
        f uu____6380  in
      let connectives =
        let uu____6392 =
          let uu____6401 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Syntax_Const.and_lid, uu____6401)  in
        let uu____6414 =
          let uu____6424 =
            let uu____6433 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Syntax_Const.or_lid, uu____6433)  in
          let uu____6446 =
            let uu____6456 =
              let uu____6466 =
                let uu____6475 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Syntax_Const.iff_lid, uu____6475)  in
              let uu____6488 =
                let uu____6498 =
                  let uu____6508 =
                    let uu____6517 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Syntax_Const.not_lid, uu____6517)  in
                  [uu____6508;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6498  in
              uu____6466 :: uu____6488  in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6456  in
          uu____6424 :: uu____6446  in
        uu____6392 :: uu____6414  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6679 = encode_formula phi' env  in
            (match uu____6679 with
             | (phi2,decls) ->
                 let uu____6686 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____6686, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6687 ->
            let uu____6692 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____6692 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6721 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____6721 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6729;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6731;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6747 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____6747 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6779::(x,uu____6781)::(t,uu____6783)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6817 = encode_term x env  in
                 (match uu____6817 with
                  | (x1,decls) ->
                      let uu____6824 = encode_term t env  in
                      (match uu____6824 with
                       | (t1,decls') ->
                           let uu____6831 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____6831, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6835)::(msg,uu____6837)::(phi2,uu____6839)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6873 =
                   let uu____6876 =
                     let uu____6877 = FStar_Syntax_Subst.compress r  in
                     uu____6877.FStar_Syntax_Syntax.n  in
                   let uu____6880 =
                     let uu____6881 = FStar_Syntax_Subst.compress msg  in
                     uu____6881.FStar_Syntax_Syntax.n  in
                   (uu____6876, uu____6880)  in
                 (match uu____6873 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6888))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1
                         in
                      fallback phi3
                  | uu____6904 -> fallback phi2)
             | uu____6907 when head_redex env head2 ->
                 let uu____6915 = whnf env phi1  in
                 encode_formula uu____6915 env
             | uu____6916 ->
                 let uu____6924 = encode_term phi1 env  in
                 (match uu____6924 with
                  | (tt,decls) ->
                      let uu____6931 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___150_6932 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___150_6932.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___150_6932.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____6931, decls)))
        | uu____6935 ->
            let uu____6936 = encode_term phi1 env  in
            (match uu____6936 with
             | (tt,decls) ->
                 let uu____6943 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___151_6944 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___151_6944.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___151_6944.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____6943, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____6971 = encode_binders None bs env1  in
        match uu____6971 with
        | (vars,guards,env2,decls,uu____6993) ->
            let uu____7000 =
              let uu____7007 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7030 =
                          let uu____7035 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7049  ->
                                    match uu____7049 with
                                    | (t,uu____7055) ->
                                        encode_term t
                                          (let uu___152_7056 = env2  in
                                           {
                                             bindings =
                                               (uu___152_7056.bindings);
                                             depth = (uu___152_7056.depth);
                                             tcenv = (uu___152_7056.tcenv);
                                             warn = (uu___152_7056.warn);
                                             cache = (uu___152_7056.cache);
                                             nolabels =
                                               (uu___152_7056.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___152_7056.encode_non_total_function_typ)
                                           })))
                             in
                          FStar_All.pipe_right uu____7035 FStar_List.unzip
                           in
                        match uu____7030 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____7007 FStar_List.unzip  in
            (match uu____7000 with
             | (pats,decls') ->
                 let uu____7108 = encode_formula body env2  in
                 (match uu____7108 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7127;
                             FStar_SMTEncoding_Term.rng = uu____7128;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7136 -> guards  in
                      let uu____7139 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____7139, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7173  ->
                   match uu____7173 with
                   | (x,uu____7177) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x))
            in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7183 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7189 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____7189) uu____7183 tl1
                in
             let uu____7191 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7203  ->
                       match uu____7203 with
                       | (b,uu____7207) ->
                           let uu____7208 = FStar_Util.set_mem b pat_vars  in
                           Prims.op_Negation uu____7208))
                in
             (match uu____7191 with
              | None  -> ()
              | Some (x,uu____7212) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____7222 =
                    let uu____7223 = FStar_Syntax_Print.bv_to_string x  in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7223
                     in
                  FStar_Errors.warn pos uu____7222)
          in
       let uu____7224 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____7224 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7230 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7266  ->
                     match uu____7266 with
                     | (l,uu____7276) -> FStar_Ident.lid_equals op l))
              in
           (match uu____7230 with
            | None  -> fallback phi1
            | Some (uu____7299,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7328 = encode_q_body env vars pats body  in
             match uu____7328 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7354 =
                     let uu____7360 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____7360)  in
                   FStar_SMTEncoding_Term.mkForall uu____7354
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7372 = encode_q_body env vars pats body  in
             match uu____7372 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7397 =
                   let uu____7398 =
                     let uu____7404 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____7404)  in
                   FStar_SMTEncoding_Term.mkExists uu____7398
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____7397, decls))))

type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl
          Prims.list)
    ;
  is: FStar_Ident.lident -> Prims.bool }
let prims : prims_t =
  let uu____7453 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____7453 with
  | (asym,a) ->
      let uu____7458 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____7458 with
       | (xsym,x) ->
           let uu____7463 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____7463 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7493 =
                      let uu____7499 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd)
                         in
                      (x1, uu____7499, FStar_SMTEncoding_Term.Term_sort,
                        None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____7493  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None)
                     in
                  let xapp =
                    let uu____7514 =
                      let uu____7518 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____7518)  in
                    FStar_SMTEncoding_Util.mkApp uu____7514  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____7526 =
                    let uu____7528 =
                      let uu____7530 =
                        let uu____7532 =
                          let uu____7533 =
                            let uu____7537 =
                              let uu____7538 =
                                let uu____7544 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____7544)  in
                              FStar_SMTEncoding_Util.mkForall uu____7538  in
                            (uu____7537, None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Term.Assume uu____7533  in
                        let uu____7553 =
                          let uu____7555 =
                            let uu____7556 =
                              let uu____7560 =
                                let uu____7561 =
                                  let uu____7567 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____7567)  in
                                FStar_SMTEncoding_Util.mkForall uu____7561
                                 in
                              (uu____7560,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Term.Assume uu____7556  in
                          [uu____7555]  in
                        uu____7532 :: uu____7553  in
                      xtok_decl :: uu____7530  in
                    xname_decl :: uu____7528  in
                  (xtok1, uu____7526)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____7616 =
                    let uu____7624 =
                      let uu____7630 =
                        let uu____7631 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7631
                         in
                      quant axy uu____7630  in
                    (FStar_Syntax_Const.op_Eq, uu____7624)  in
                  let uu____7637 =
                    let uu____7646 =
                      let uu____7654 =
                        let uu____7660 =
                          let uu____7661 =
                            let uu____7662 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____7662  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7661
                           in
                        quant axy uu____7660  in
                      (FStar_Syntax_Const.op_notEq, uu____7654)  in
                    let uu____7668 =
                      let uu____7677 =
                        let uu____7685 =
                          let uu____7691 =
                            let uu____7692 =
                              let uu____7693 =
                                let uu____7696 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____7697 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____7696, uu____7697)  in
                              FStar_SMTEncoding_Util.mkLT uu____7693  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7692
                             in
                          quant xy uu____7691  in
                        (FStar_Syntax_Const.op_LT, uu____7685)  in
                      let uu____7703 =
                        let uu____7712 =
                          let uu____7720 =
                            let uu____7726 =
                              let uu____7727 =
                                let uu____7728 =
                                  let uu____7731 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____7732 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____7731, uu____7732)  in
                                FStar_SMTEncoding_Util.mkLTE uu____7728  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7727
                               in
                            quant xy uu____7726  in
                          (FStar_Syntax_Const.op_LTE, uu____7720)  in
                        let uu____7738 =
                          let uu____7747 =
                            let uu____7755 =
                              let uu____7761 =
                                let uu____7762 =
                                  let uu____7763 =
                                    let uu____7766 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____7767 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____7766, uu____7767)  in
                                  FStar_SMTEncoding_Util.mkGT uu____7763  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7762
                                 in
                              quant xy uu____7761  in
                            (FStar_Syntax_Const.op_GT, uu____7755)  in
                          let uu____7773 =
                            let uu____7782 =
                              let uu____7790 =
                                let uu____7796 =
                                  let uu____7797 =
                                    let uu____7798 =
                                      let uu____7801 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____7802 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____7801, uu____7802)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____7798
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7797
                                   in
                                quant xy uu____7796  in
                              (FStar_Syntax_Const.op_GTE, uu____7790)  in
                            let uu____7808 =
                              let uu____7817 =
                                let uu____7825 =
                                  let uu____7831 =
                                    let uu____7832 =
                                      let uu____7833 =
                                        let uu____7836 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____7837 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____7836, uu____7837)  in
                                      FStar_SMTEncoding_Util.mkSub uu____7833
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7832
                                     in
                                  quant xy uu____7831  in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7825)
                                 in
                              let uu____7843 =
                                let uu____7852 =
                                  let uu____7860 =
                                    let uu____7866 =
                                      let uu____7867 =
                                        let uu____7868 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7868
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7867
                                       in
                                    quant qx uu____7866  in
                                  (FStar_Syntax_Const.op_Minus, uu____7860)
                                   in
                                let uu____7874 =
                                  let uu____7883 =
                                    let uu____7891 =
                                      let uu____7897 =
                                        let uu____7898 =
                                          let uu____7899 =
                                            let uu____7902 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____7903 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____7902, uu____7903)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7899
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7898
                                         in
                                      quant xy uu____7897  in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7891)
                                     in
                                  let uu____7909 =
                                    let uu____7918 =
                                      let uu____7926 =
                                        let uu____7932 =
                                          let uu____7933 =
                                            let uu____7934 =
                                              let uu____7937 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____7938 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____7937, uu____7938)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7934
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7933
                                           in
                                        quant xy uu____7932  in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7926)
                                       in
                                    let uu____7944 =
                                      let uu____7953 =
                                        let uu____7961 =
                                          let uu____7967 =
                                            let uu____7968 =
                                              let uu____7969 =
                                                let uu____7972 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____7973 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____7972, uu____7973)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7969
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7968
                                             in
                                          quant xy uu____7967  in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7961)
                                         in
                                      let uu____7979 =
                                        let uu____7988 =
                                          let uu____7996 =
                                            let uu____8002 =
                                              let uu____8003 =
                                                let uu____8004 =
                                                  let uu____8007 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____8008 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____8007, uu____8008)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8004
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8003
                                               in
                                            quant xy uu____8002  in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____7996)
                                           in
                                        let uu____8014 =
                                          let uu____8023 =
                                            let uu____8031 =
                                              let uu____8037 =
                                                let uu____8038 =
                                                  let uu____8039 =
                                                    let uu____8042 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____8043 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____8042, uu____8043)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8039
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8038
                                                 in
                                              quant xy uu____8037  in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8031)
                                             in
                                          let uu____8049 =
                                            let uu____8058 =
                                              let uu____8066 =
                                                let uu____8072 =
                                                  let uu____8073 =
                                                    let uu____8074 =
                                                      let uu____8077 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____8078 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____8077,
                                                        uu____8078)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8074
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8073
                                                   in
                                                quant xy uu____8072  in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8066)
                                               in
                                            let uu____8084 =
                                              let uu____8093 =
                                                let uu____8101 =
                                                  let uu____8107 =
                                                    let uu____8108 =
                                                      let uu____8109 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8109
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8108
                                                     in
                                                  quant qx uu____8107  in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8101)
                                                 in
                                              [uu____8093]  in
                                            uu____8058 :: uu____8084  in
                                          uu____8023 :: uu____8049  in
                                        uu____7988 :: uu____8014  in
                                      uu____7953 :: uu____7979  in
                                    uu____7918 :: uu____7944  in
                                  uu____7883 :: uu____7909  in
                                uu____7852 :: uu____7874  in
                              uu____7817 :: uu____7843  in
                            uu____7782 :: uu____7808  in
                          uu____7747 :: uu____7773  in
                        uu____7712 :: uu____7738  in
                      uu____7677 :: uu____7703  in
                    uu____7646 :: uu____7668  in
                  uu____7616 :: uu____7637  in
                let mk1 l v1 =
                  let uu____8237 =
                    let uu____8242 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8274  ->
                              match uu____8274 with
                              | (l',uu____8283) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____8242
                      (FStar_Option.map
                         (fun uu____8316  ->
                            match uu____8316 with | (uu____8327,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____8237 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8368  ->
                          match uu____8368 with
                          | (l',uu____8377) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let pretype_axiom :
  FStar_SMTEncoding_Term.term ->
    (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.decl
  =
  fun tapp  ->
    fun vars  ->
      let uu____8400 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      match uu____8400 with
      | (xxsym,xx) ->
          let uu____8405 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
             in
          (match uu____8405 with
           | (ffsym,ff) ->
               let xx_has_type =
                 FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
               let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
               let uu____8412 =
                 let uu____8416 =
                   let uu____8417 =
                     let uu____8423 =
                       let uu____8424 =
                         let uu____8427 =
                           let uu____8428 =
                             let uu____8431 =
                               FStar_SMTEncoding_Util.mkApp ("PreType", [xx])
                                in
                             (tapp, uu____8431)  in
                           FStar_SMTEncoding_Util.mkEq uu____8428  in
                         (xx_has_type, uu____8427)  in
                       FStar_SMTEncoding_Util.mkImp uu____8424  in
                     ([[xx_has_type]],
                       ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                       (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                       uu____8423)
                      in
                   FStar_SMTEncoding_Util.mkForall uu____8417  in
                 let uu____8444 =
                   let uu____8445 =
                     let uu____8446 = FStar_Util.digest_of_string tapp_hash
                        in
                     Prims.strcat "pretyping_" uu____8446  in
                   varops.mk_unique uu____8445  in
                 (uu____8416, (Some "pretyping"), uu____8444)  in
               FStar_SMTEncoding_Term.Assume uu____8412)
  
let primitive_type_axioms :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
  let x = FStar_SMTEncoding_Util.mkFreeV xx  in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort)  in
  let y = FStar_SMTEncoding_Util.mkFreeV yy  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____8476 =
      let uu____8477 =
        let uu____8481 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____8481, (Some "unit typing"), "unit_typing")  in
      FStar_SMTEncoding_Term.Assume uu____8477  in
    let uu____8483 =
      let uu____8485 =
        let uu____8486 =
          let uu____8490 =
            let uu____8491 =
              let uu____8497 =
                let uu____8498 =
                  let uu____8501 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____8501)  in
                FStar_SMTEncoding_Util.mkImp uu____8498  in
              ([[typing_pred]], [xx], uu____8497)  in
            mkForall_fuel uu____8491  in
          (uu____8490, (Some "unit inversion"), "unit_inversion")  in
        FStar_SMTEncoding_Term.Assume uu____8486  in
      [uu____8485]  in
    uu____8476 :: uu____8483  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____8529 =
      let uu____8530 =
        let uu____8534 =
          let uu____8535 =
            let uu____8541 =
              let uu____8544 =
                let uu____8546 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____8546]  in
              [uu____8544]  in
            let uu____8549 =
              let uu____8550 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8550 tt  in
            (uu____8541, [bb], uu____8549)  in
          FStar_SMTEncoding_Util.mkForall uu____8535  in
        (uu____8534, (Some "bool typing"), "bool_typing")  in
      FStar_SMTEncoding_Term.Assume uu____8530  in
    let uu____8561 =
      let uu____8563 =
        let uu____8564 =
          let uu____8568 =
            let uu____8569 =
              let uu____8575 =
                let uu____8576 =
                  let uu____8579 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x  in
                  (typing_pred, uu____8579)  in
                FStar_SMTEncoding_Util.mkImp uu____8576  in
              ([[typing_pred]], [xx], uu____8575)  in
            mkForall_fuel uu____8569  in
          (uu____8568, (Some "bool inversion"), "bool_inversion")  in
        FStar_SMTEncoding_Term.Assume uu____8564  in
      [uu____8563]  in
    uu____8529 :: uu____8561  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____8613 =
        let uu____8614 =
          let uu____8618 =
            let uu____8620 =
              let uu____8622 =
                let uu____8624 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____8625 =
                  let uu____8627 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____8627]  in
                uu____8624 :: uu____8625  in
              tt :: uu____8622  in
            tt :: uu____8620  in
          ("Prims.Precedes", uu____8618)  in
        FStar_SMTEncoding_Util.mkApp uu____8614  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8613  in
    let precedes_y_x =
      let uu____8630 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8630  in
    let uu____8632 =
      let uu____8633 =
        let uu____8637 =
          let uu____8638 =
            let uu____8644 =
              let uu____8647 =
                let uu____8649 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____8649]  in
              [uu____8647]  in
            let uu____8652 =
              let uu____8653 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8653 tt  in
            (uu____8644, [bb], uu____8652)  in
          FStar_SMTEncoding_Util.mkForall uu____8638  in
        (uu____8637, (Some "int typing"), "int_typing")  in
      FStar_SMTEncoding_Term.Assume uu____8633  in
    let uu____8664 =
      let uu____8666 =
        let uu____8667 =
          let uu____8671 =
            let uu____8672 =
              let uu____8678 =
                let uu____8679 =
                  let uu____8682 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x  in
                  (typing_pred, uu____8682)  in
                FStar_SMTEncoding_Util.mkImp uu____8679  in
              ([[typing_pred]], [xx], uu____8678)  in
            mkForall_fuel uu____8672  in
          (uu____8671, (Some "int inversion"), "int_inversion")  in
        FStar_SMTEncoding_Term.Assume uu____8667  in
      let uu____8695 =
        let uu____8697 =
          let uu____8698 =
            let uu____8702 =
              let uu____8703 =
                let uu____8709 =
                  let uu____8710 =
                    let uu____8713 =
                      let uu____8714 =
                        let uu____8716 =
                          let uu____8718 =
                            let uu____8720 =
                              let uu____8721 =
                                let uu____8724 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____8725 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____8724, uu____8725)  in
                              FStar_SMTEncoding_Util.mkGT uu____8721  in
                            let uu____8726 =
                              let uu____8728 =
                                let uu____8729 =
                                  let uu____8732 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____8733 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____8732, uu____8733)  in
                                FStar_SMTEncoding_Util.mkGTE uu____8729  in
                              let uu____8734 =
                                let uu____8736 =
                                  let uu____8737 =
                                    let uu____8740 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____8741 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____8740, uu____8741)  in
                                  FStar_SMTEncoding_Util.mkLT uu____8737  in
                                [uu____8736]  in
                              uu____8728 :: uu____8734  in
                            uu____8720 :: uu____8726  in
                          typing_pred_y :: uu____8718  in
                        typing_pred :: uu____8716  in
                      FStar_SMTEncoding_Util.mk_and_l uu____8714  in
                    (uu____8713, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____8710  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8709)
                 in
              mkForall_fuel uu____8703  in
            (uu____8702, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Term.Assume uu____8698  in
        [uu____8697]  in
      uu____8666 :: uu____8695  in
    uu____8632 :: uu____8664  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____8771 =
      let uu____8772 =
        let uu____8776 =
          let uu____8777 =
            let uu____8783 =
              let uu____8786 =
                let uu____8788 = FStar_SMTEncoding_Term.boxString b  in
                [uu____8788]  in
              [uu____8786]  in
            let uu____8791 =
              let uu____8792 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8792 tt  in
            (uu____8783, [bb], uu____8791)  in
          FStar_SMTEncoding_Util.mkForall uu____8777  in
        (uu____8776, (Some "string typing"), "string_typing")  in
      FStar_SMTEncoding_Term.Assume uu____8772  in
    let uu____8803 =
      let uu____8805 =
        let uu____8806 =
          let uu____8810 =
            let uu____8811 =
              let uu____8817 =
                let uu____8818 =
                  let uu____8821 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x  in
                  (typing_pred, uu____8821)  in
                FStar_SMTEncoding_Util.mkImp uu____8818  in
              ([[typing_pred]], [xx], uu____8817)  in
            mkForall_fuel uu____8811  in
          (uu____8810, (Some "string inversion"), "string_inversion")  in
        FStar_SMTEncoding_Term.Assume uu____8806  in
      [uu____8805]  in
    uu____8771 :: uu____8803  in
  let mk_ref1 env reft_name uu____8843 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort)  in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let refa =
      let uu____8854 =
        let uu____8858 =
          let uu____8860 = FStar_SMTEncoding_Util.mkFreeV aa  in [uu____8860]
           in
        (reft_name, uu____8858)  in
      FStar_SMTEncoding_Util.mkApp uu____8854  in
    let refb =
      let uu____8863 =
        let uu____8867 =
          let uu____8869 = FStar_SMTEncoding_Util.mkFreeV bb  in [uu____8869]
           in
        (reft_name, uu____8867)  in
      FStar_SMTEncoding_Util.mkApp uu____8863  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa  in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb  in
    let uu____8873 =
      let uu____8874 =
        let uu____8878 =
          let uu____8879 =
            let uu____8885 =
              let uu____8886 =
                let uu____8889 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x
                   in
                (typing_pred, uu____8889)  in
              FStar_SMTEncoding_Util.mkImp uu____8886  in
            ([[typing_pred]], [xx; aa], uu____8885)  in
          mkForall_fuel uu____8879  in
        (uu____8878, (Some "ref inversion"), "ref_inversion")  in
      FStar_SMTEncoding_Term.Assume uu____8874  in
    let uu____8904 =
      let uu____8906 =
        let uu____8907 =
          let uu____8911 =
            let uu____8912 =
              let uu____8918 =
                let uu____8919 =
                  let uu____8922 =
                    FStar_SMTEncoding_Util.mkAnd (typing_pred, typing_pred_b)
                     in
                  let uu____8923 =
                    let uu____8924 =
                      let uu____8927 = FStar_SMTEncoding_Util.mkFreeV aa  in
                      let uu____8928 = FStar_SMTEncoding_Util.mkFreeV bb  in
                      (uu____8927, uu____8928)  in
                    FStar_SMTEncoding_Util.mkEq uu____8924  in
                  (uu____8922, uu____8923)  in
                FStar_SMTEncoding_Util.mkImp uu____8919  in
              ([[typing_pred; typing_pred_b]], [xx; aa; bb], uu____8918)  in
            mkForall_fuel' (Prims.parse_int "2") uu____8912  in
          (uu____8911, (Some "ref typing is injective"), "ref_injectivity")
           in
        FStar_SMTEncoding_Term.Assume uu____8907  in
      [uu____8906]  in
    uu____8873 :: uu____8904  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____8970 =
      let uu____8971 =
        let uu____8975 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____8975, (Some "False interpretation"), "false_interp")  in
      FStar_SMTEncoding_Term.Assume uu____8971  in
    [uu____8970]  in
  let mk_and_interp env conj uu____8986 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____8996 =
        let uu____9000 =
          let uu____9002 = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
          [uu____9002]  in
        ("Valid", uu____9000)  in
      FStar_SMTEncoding_Util.mkApp uu____8996  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9009 =
      let uu____9010 =
        let uu____9014 =
          let uu____9015 =
            let uu____9021 =
              let uu____9022 =
                let uu____9025 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____9025, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9022  in
            ([[valid]], [aa; bb], uu____9021)  in
          FStar_SMTEncoding_Util.mkForall uu____9015  in
        (uu____9014, (Some "/\\ interpretation"), "l_and-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9010  in
    [uu____9009]  in
  let mk_or_interp env disj uu____9049 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9059 =
        let uu____9063 =
          let uu____9065 = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
          [uu____9065]  in
        ("Valid", uu____9063)  in
      FStar_SMTEncoding_Util.mkApp uu____9059  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9072 =
      let uu____9073 =
        let uu____9077 =
          let uu____9078 =
            let uu____9084 =
              let uu____9085 =
                let uu____9088 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____9088, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9085  in
            ([[valid]], [aa; bb], uu____9084)  in
          FStar_SMTEncoding_Util.mkForall uu____9078  in
        (uu____9077, (Some "\\/ interpretation"), "l_or-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9073  in
    [uu____9072]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let valid =
      let uu____9126 =
        let uu____9130 =
          let uu____9132 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])
             in
          [uu____9132]  in
        ("Valid", uu____9130)  in
      FStar_SMTEncoding_Util.mkApp uu____9126  in
    let uu____9135 =
      let uu____9136 =
        let uu____9140 =
          let uu____9141 =
            let uu____9147 =
              let uu____9148 =
                let uu____9151 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____9151, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9148  in
            ([[valid]], [aa; xx1; yy1], uu____9147)  in
          FStar_SMTEncoding_Util.mkForall uu____9141  in
        (uu____9140, (Some "Eq2 interpretation"), "eq2-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9136  in
    [uu____9135]  in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let valid =
      let uu____9195 =
        let uu____9199 =
          let uu____9201 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1])
             in
          [uu____9201]  in
        ("Valid", uu____9199)  in
      FStar_SMTEncoding_Util.mkApp uu____9195  in
    let uu____9204 =
      let uu____9205 =
        let uu____9209 =
          let uu____9210 =
            let uu____9216 =
              let uu____9217 =
                let uu____9220 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____9220, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9217  in
            ([[valid]], [aa; bb; xx1; yy1], uu____9216)  in
          FStar_SMTEncoding_Util.mkForall uu____9210  in
        (uu____9209, (Some "Eq3 interpretation"), "eq3-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9205  in
    [uu____9204]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9258 =
        let uu____9262 =
          let uu____9264 = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
          [uu____9264]  in
        ("Valid", uu____9262)  in
      FStar_SMTEncoding_Util.mkApp uu____9258  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9271 =
      let uu____9272 =
        let uu____9276 =
          let uu____9277 =
            let uu____9283 =
              let uu____9284 =
                let uu____9287 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____9287, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9284  in
            ([[valid]], [aa; bb], uu____9283)  in
          FStar_SMTEncoding_Util.mkForall uu____9277  in
        (uu____9276, (Some "==> interpretation"), "l_imp-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9272  in
    [uu____9271]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9321 =
        let uu____9325 =
          let uu____9327 = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
          [uu____9327]  in
        ("Valid", uu____9325)  in
      FStar_SMTEncoding_Util.mkApp uu____9321  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9334 =
      let uu____9335 =
        let uu____9339 =
          let uu____9340 =
            let uu____9346 =
              let uu____9347 =
                let uu____9350 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____9350, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9347  in
            ([[valid]], [aa; bb], uu____9346)  in
          FStar_SMTEncoding_Util.mkForall uu____9340  in
        (uu____9339, (Some "<==> interpretation"), "l_iff-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9335  in
    [uu____9334]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let valid =
      let uu____9380 =
        let uu____9384 =
          let uu____9386 = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
          [uu____9386]  in
        ("Valid", uu____9384)  in
      FStar_SMTEncoding_Util.mkApp uu____9380  in
    let not_valid_a =
      let uu____9390 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9390  in
    let uu____9392 =
      let uu____9393 =
        let uu____9397 =
          let uu____9398 =
            let uu____9404 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[valid]], [aa], uu____9404)  in
          FStar_SMTEncoding_Util.mkForall uu____9398  in
        (uu____9397, (Some "not interpretation"), "l_not-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9393  in
    [uu____9392]  in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let valid =
      let uu____9440 =
        let uu____9444 =
          let uu____9446 = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b])
             in
          [uu____9446]  in
        ("Valid", uu____9444)  in
      FStar_SMTEncoding_Util.mkApp uu____9440  in
    let valid_b_x =
      let uu____9450 =
        let uu____9454 =
          let uu____9456 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____9456]  in
        ("Valid", uu____9454)  in
      FStar_SMTEncoding_Util.mkApp uu____9450  in
    let uu____9458 =
      let uu____9459 =
        let uu____9463 =
          let uu____9464 =
            let uu____9470 =
              let uu____9471 =
                let uu____9474 =
                  let uu____9475 =
                    let uu____9481 =
                      let uu____9484 =
                        let uu____9486 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____9486]  in
                      [uu____9484]  in
                    let uu____9489 =
                      let uu____9490 =
                        let uu____9493 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____9493, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____9490  in
                    (uu____9481, [xx1], uu____9489)  in
                  FStar_SMTEncoding_Util.mkForall uu____9475  in
                (uu____9474, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9471  in
            ([[valid]], [aa; bb], uu____9470)  in
          FStar_SMTEncoding_Util.mkForall uu____9464  in
        (uu____9463, (Some "forall interpretation"), "forall-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9459  in
    [uu____9458]  in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let valid =
      let uu____9540 =
        let uu____9544 =
          let uu____9546 = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b])
             in
          [uu____9546]  in
        ("Valid", uu____9544)  in
      FStar_SMTEncoding_Util.mkApp uu____9540  in
    let valid_b_x =
      let uu____9550 =
        let uu____9554 =
          let uu____9556 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____9556]  in
        ("Valid", uu____9554)  in
      FStar_SMTEncoding_Util.mkApp uu____9550  in
    let uu____9558 =
      let uu____9559 =
        let uu____9563 =
          let uu____9564 =
            let uu____9570 =
              let uu____9571 =
                let uu____9574 =
                  let uu____9575 =
                    let uu____9581 =
                      let uu____9584 =
                        let uu____9586 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____9586]  in
                      [uu____9584]  in
                    let uu____9589 =
                      let uu____9590 =
                        let uu____9593 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____9593, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____9590  in
                    (uu____9581, [xx1], uu____9589)  in
                  FStar_SMTEncoding_Util.mkExists uu____9575  in
                (uu____9574, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9571  in
            ([[valid]], [aa; bb], uu____9570)  in
          FStar_SMTEncoding_Util.mkForall uu____9564  in
        (uu____9563, (Some "exists interpretation"), "exists-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9559  in
    [uu____9558]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____9629 =
      let uu____9630 =
        let uu____9634 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty
           in
        let uu____9635 = varops.mk_unique "typing_range_const"  in
        (uu____9634, (Some "Range_const typing"), uu____9635)  in
      FStar_SMTEncoding_Term.Assume uu____9630  in
    [uu____9629]  in
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
    (FStar_Syntax_Const.range_lid, mk_range_interp)]  in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____9897 =
            FStar_Util.find_opt
              (fun uu____9915  ->
                 match uu____9915 with
                 | (l,uu____9925) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____9897 with
          | None  -> []
          | Some (uu____9947,f) -> f env s tt
  
let encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____9984 = encode_function_type_as_formula None None t env  in
        match uu____9984 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Term.Assume
                 (form, (Some (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
  
let encode_free_var :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun fv  ->
      fun tt  ->
        fun t_norm  ->
          fun quals  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____10016 =
              (let uu____10017 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm)
                  in
               FStar_All.pipe_left Prims.op_Negation uu____10017) ||
                (FStar_Syntax_Util.is_lemma t_norm)
               in
            if uu____10016
            then
              let uu____10021 = new_term_constant_and_tok_from_lid env lid
                 in
              match uu____10021 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10033 =
                      let uu____10034 = FStar_Syntax_Subst.compress t_norm
                         in
                      uu____10034.FStar_Syntax_Syntax.n  in
                    match uu____10033 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10039) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10056  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10059 -> []  in
                  let d =
                    FStar_SMTEncoding_Term.DeclFun
                      (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                        (Some
                           "Uninterpreted function symbol for impure function"))
                     in
                  let dd =
                    FStar_SMTEncoding_Term.DeclFun
                      (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Uninterpreted name for impure function"))
                     in
                  ([d; dd], env1)
            else
              (let uu____10068 = prims.is lid  in
               if uu____10068
               then
                 let vname = varops.new_fvar lid  in
                 let uu____10073 = prims.mk lid vname  in
                 match uu____10073 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok)  in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims"  in
                  let uu____10088 =
                    let uu____10094 = curried_arrow_formals_comp t_norm  in
                    match uu____10094 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10105 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp
                             in
                          if uu____10105
                          then
                            let uu____10106 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___153_10107 = env.tcenv  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___153_10107.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___153_10107.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___153_10107.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___153_10107.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___153_10107.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___153_10107.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___153_10107.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___153_10107.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___153_10107.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___153_10107.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___153_10107.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___153_10107.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___153_10107.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___153_10107.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___153_10107.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___153_10107.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___153_10107.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___153_10107.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___153_10107.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___153_10107.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___153_10107.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___153_10107.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___153_10107.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown
                               in
                            FStar_Syntax_Syntax.mk_Total uu____10106
                          else comp  in
                        if encode_non_total_function_typ
                        then
                          let uu____10114 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1
                             in
                          (args, uu____10114)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1)))
                     in
                  match uu____10088 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10141 =
                        new_term_constant_and_tok_from_lid env lid  in
                      (match uu____10141 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10154 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, [])
                              in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___124_10178  ->
                                     match uu___124_10178 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10181 =
                                           FStar_Util.prefix vars  in
                                         (match uu____10181 with
                                          | (uu____10192,(xxsym,uu____10194))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              let uu____10204 =
                                                let uu____10205 =
                                                  let uu____10209 =
                                                    let uu____10210 =
                                                      let uu____10216 =
                                                        let uu____10217 =
                                                          let uu____10220 =
                                                            let uu____10221 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10221
                                                             in
                                                          (vapp, uu____10220)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10217
                                                         in
                                                      ([[vapp]], vars,
                                                        uu____10216)
                                                       in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10210
                                                     in
                                                  (uu____10209,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str)))
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10205
                                                 in
                                              [uu____10204])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10232 =
                                           FStar_Util.prefix vars  in
                                         (match uu____10232 with
                                          | (uu____10243,(xxsym,uu____10245))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              let f1 =
                                                {
                                                  FStar_Syntax_Syntax.ppname
                                                    = f;
                                                  FStar_Syntax_Syntax.index =
                                                    (Prims.parse_int "0");
                                                  FStar_Syntax_Syntax.sort =
                                                    FStar_Syntax_Syntax.tun
                                                }  in
                                              let tp_name =
                                                mk_term_projector_name d f1
                                                 in
                                              let prim_app =
                                                FStar_SMTEncoding_Util.mkApp
                                                  (tp_name, [xx])
                                                 in
                                              let uu____10259 =
                                                let uu____10260 =
                                                  let uu____10264 =
                                                    let uu____10265 =
                                                      let uu____10271 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app)
                                                         in
                                                      ([[vapp]], vars,
                                                        uu____10271)
                                                       in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10265
                                                     in
                                                  (uu____10264,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name))
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10260
                                                 in
                                              [uu____10259])
                                     | uu____10280 -> []))
                              in
                           let uu____10281 = encode_binders None formals env1
                              in
                           (match uu____10281 with
                            | (vars,guards,env',decls1,uu____10297) ->
                                let uu____10304 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10309 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards
                                         in
                                      (uu____10309, decls1)
                                  | Some p ->
                                      let uu____10311 = encode_formula p env'
                                         in
                                      (match uu____10311 with
                                       | (g,ds) ->
                                           let uu____10318 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards)
                                              in
                                           (uu____10318,
                                             (FStar_List.append decls1 ds)))
                                   in
                                (match uu____10304 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars  in
                                     let vapp =
                                       let uu____10327 =
                                         let uu____10331 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars
                                            in
                                         (vname, uu____10331)  in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10327
                                        in
                                     let uu____10336 =
                                       let vname_decl =
                                         let uu____10341 =
                                           let uu____10347 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10352  ->
                                                     FStar_SMTEncoding_Term.Term_sort))
                                              in
                                           (vname, uu____10347,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None)
                                            in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10341
                                          in
                                       let uu____10357 =
                                         let env2 =
                                           let uu___154_10361 = env1  in
                                           {
                                             bindings =
                                               (uu___154_10361.bindings);
                                             depth = (uu___154_10361.depth);
                                             tcenv = (uu___154_10361.tcenv);
                                             warn = (uu___154_10361.warn);
                                             cache = (uu___154_10361.cache);
                                             nolabels =
                                               (uu___154_10361.nolabels);
                                             use_zfuel_name =
                                               (uu___154_10361.use_zfuel_name);
                                             encode_non_total_function_typ
                                           }  in
                                         let uu____10362 =
                                           let uu____10363 =
                                             head_normal env2 tt  in
                                           Prims.op_Negation uu____10363  in
                                         if uu____10362
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm
                                          in
                                       match uu____10357 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             FStar_SMTEncoding_Term.Assume
                                               (tok_typing,
                                                 (Some
                                                    "function token typing"),
                                                 (Prims.strcat
                                                    "function_token_typing_"
                                                    vname))
                                              in
                                           let uu____10374 =
                                             match formals with
                                             | [] ->
                                                 let uu____10383 =
                                                   let uu____10384 =
                                                     let uu____10386 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort)
                                                        in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10386
                                                      in
                                                   push_free_var env1 lid
                                                     vname uu____10384
                                                    in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10383)
                                             | uu____10389 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None)
                                                    in
                                                 let vtok_fresh =
                                                   let uu____10394 =
                                                     varops.next_id ()  in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10394
                                                    in
                                                 let name_tok_corr =
                                                   let uu____10396 =
                                                     let uu____10400 =
                                                       let uu____10401 =
                                                         let uu____10407 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp)
                                                            in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10407)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10401
                                                        in
                                                     (uu____10400,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname))
                                                      in
                                                   FStar_SMTEncoding_Term.Assume
                                                     uu____10396
                                                    in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1)
                                              in
                                           (match uu____10374 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2))
                                        in
                                     (match uu____10336 with
                                      | (decls2,env2) ->
                                          let uu____10431 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t
                                               in
                                            let uu____10436 =
                                              encode_term res_t1 env'  in
                                            match uu____10436 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10444 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t
                                                   in
                                                (encoded_res_t, uu____10444,
                                                  decls)
                                             in
                                          (match uu____10431 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10452 =
                                                   let uu____10456 =
                                                     let uu____10457 =
                                                       let uu____10463 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred)
                                                          in
                                                       ([[vapp]], vars,
                                                         uu____10463)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10457
                                                      in
                                                   (uu____10456,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname))
                                                    in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____10452
                                                  in
                                               let freshness =
                                                 let uu____10472 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New)
                                                    in
                                                 if uu____10472
                                                 then
                                                   let uu____10475 =
                                                     let uu____10476 =
                                                       let uu____10482 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd)
                                                          in
                                                       let uu____10488 =
                                                         varops.next_id ()
                                                          in
                                                       (vname, uu____10482,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10488)
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10476
                                                      in
                                                   let uu____10490 =
                                                     let uu____10492 =
                                                       pretype_axiom vapp
                                                         vars
                                                        in
                                                     [uu____10492]  in
                                                   uu____10475 :: uu____10490
                                                 else []  in
                                               let g =
                                                 let uu____10496 =
                                                   let uu____10498 =
                                                     let uu____10500 =
                                                       let uu____10502 =
                                                         let uu____10504 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars
                                                            in
                                                         typingAx ::
                                                           uu____10504
                                                          in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10502
                                                        in
                                                     FStar_List.append decls3
                                                       uu____10500
                                                      in
                                                   FStar_List.append decls2
                                                     uu____10498
                                                    in
                                                 FStar_List.append decls11
                                                   uu____10496
                                                  in
                                               (g, env2))))))))
  
let declare_top_level_let :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string * FStar_SMTEncoding_Term.term Prims.option) *
            FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____10526 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____10526 with
          | None  ->
              let uu____10549 = encode_free_var env x t t_norm []  in
              (match uu____10549 with
               | (decls,env1) ->
                   let uu____10564 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____10564 with
                    | (n1,x',uu____10583) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10595) -> ((n1, x1), [], env)
  
let encode_top_level_val :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun lid  ->
      fun t  ->
        fun quals  ->
          let tt = norm env t  in
          let uu____10628 = encode_free_var env lid t tt quals  in
          match uu____10628 with
          | (decls,env1) ->
              let uu____10639 = FStar_Syntax_Util.is_smt_lemma t  in
              if uu____10639
              then
                let uu____10643 =
                  let uu____10645 = encode_smt_lemma env1 lid tt  in
                  FStar_List.append decls uu____10645  in
                (uu____10643, env1)
              else (decls, env1)
  
let encode_top_level_vals :
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____10673  ->
                fun lb  ->
                  match uu____10673 with
                  | (decls,env1) ->
                      let uu____10685 =
                        let uu____10689 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val env1 uu____10689
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____10685 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let is_tactic : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____10703 = FStar_Syntax_Util.head_and_args t  in
    match uu____10703 with
    | (hd1,args) ->
        let uu____10729 =
          let uu____10730 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10730.FStar_Syntax_Syntax.n  in
        (match uu____10729 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10734,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10747 -> false)
  
let encode_top_level_let :
  env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun uu____10762  ->
      fun quals  ->
        match uu____10762 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____10811 = FStar_Util.first_N nbinders formals  in
              match uu____10811 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10851  ->
                         fun uu____10852  ->
                           match (uu____10851, uu____10852) with
                           | ((formal,uu____10862),(binder,uu____10864)) ->
                               let uu____10869 =
                                 let uu____10874 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____10874)  in
                               FStar_Syntax_Syntax.NT uu____10869) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____10879 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10893  ->
                              match uu____10893 with
                              | (x,i) ->
                                  let uu____10900 =
                                    let uu___155_10901 = x  in
                                    let uu____10902 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___155_10901.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___155_10901.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10902
                                    }  in
                                  (uu____10900, i)))
                       in
                    FStar_All.pipe_right uu____10879
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____10914 =
                      let uu____10916 =
                        let uu____10917 = FStar_Syntax_Subst.subst subst1 t
                           in
                        uu____10917.FStar_Syntax_Syntax.n  in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10916
                       in
                    let uu____10921 =
                      let uu____10922 = FStar_Syntax_Subst.compress body  in
                      let uu____10923 =
                        let uu____10924 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left Prims.snd uu____10924  in
                      FStar_Syntax_Syntax.extend_app_n uu____10922
                        uu____10923
                       in
                    uu____10921 uu____10914 body.FStar_Syntax_Syntax.pos  in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10966 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____10966
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___156_10967 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___156_10967.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___156_10967.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___156_10967.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___156_10967.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___156_10967.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___156_10967.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___156_10967.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___156_10967.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___156_10967.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___156_10967.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___156_10967.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___156_10967.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___156_10967.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___156_10967.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___156_10967.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___156_10967.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___156_10967.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___156_10967.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___156_10967.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___156_10967.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___156_10967.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___156_10967.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___156_10967.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____10988 = FStar_Syntax_Util.abs_formals e  in
                match uu____10988 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11037::uu____11038 ->
                         let uu____11046 =
                           let uu____11047 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____11047.FStar_Syntax_Syntax.n  in
                         (match uu____11046 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11074 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____11074 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____11100 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____11100
                                   then
                                     let uu____11118 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____11118 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11164  ->
                                                   fun uu____11165  ->
                                                     match (uu____11164,
                                                             uu____11165)
                                                     with
                                                     | ((x,uu____11175),
                                                        (b,uu____11177)) ->
                                                         let uu____11182 =
                                                           let uu____11187 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____11187)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11182)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____11189 =
                                            let uu____11200 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____11200)
                                             in
                                          (uu____11189, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11235 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____11235 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11287) ->
                              let uu____11292 =
                                let uu____11303 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                Prims.fst uu____11303  in
                              (uu____11292, true)
                          | uu____11336 when Prims.op_Negation norm1 ->
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
                                  env.tcenv t_norm1
                                 in
                              aux true t_norm2
                          | uu____11338 ->
                              let uu____11339 =
                                let uu____11340 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____11341 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11340
                                  uu____11341
                                 in
                              failwith uu____11339)
                     | uu____11354 ->
                         let uu____11355 =
                           let uu____11356 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____11356.FStar_Syntax_Syntax.n  in
                         (match uu____11355 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11383 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____11383 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1  in
                                   let uu____11401 =
                                     eta_expand1 [] formals1 e tres  in
                                   (match uu____11401 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11449 -> (([], e, [], t_norm1), false)))
                 in
              aux false t_norm  in
            (try
               let uu____11477 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____11477
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11484 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11525  ->
                            fun lb  ->
                              match uu____11525 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11576 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____11576
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____11579 =
                                      let uu____11587 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____11587
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____11579 with
                                    | (tok,decl,env2) ->
                                        let uu____11612 =
                                          let uu____11619 =
                                            let uu____11625 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            (uu____11625, tok)  in
                                          uu____11619 :: toks  in
                                        (uu____11612, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____11484 with
                  | (toks,typs,decls,env1) ->
                      let toks1 = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 curry f ftok vars =
                        match vars with
                        | [] ->
                            FStar_SMTEncoding_Util.mkFreeV
                              (f, FStar_SMTEncoding_Term.Term_sort)
                        | uu____11727 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11732 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   mk_Apply uu____11732 vars)
                            else
                              (let uu____11734 =
                                 let uu____11738 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars
                                    in
                                 (f, uu____11738)  in
                               FStar_SMTEncoding_Util.mkApp uu____11734)
                         in
                      let uu____11743 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___125_11745  ->
                                 match uu___125_11745 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11746 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11749 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11749)))
                         in
                      if uu____11743
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11769;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11771;
                                FStar_Syntax_Syntax.lbeff = uu____11772;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  in
                               let uu____11813 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               (match uu____11813 with
                                | (univ_subst,univ_vars1) ->
                                    let env' =
                                      let uu___159_11828 = env1  in
                                      let uu____11829 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1.tcenv univ_vars1
                                         in
                                      {
                                        bindings = (uu___159_11828.bindings);
                                        depth = (uu___159_11828.depth);
                                        tcenv = uu____11829;
                                        warn = (uu___159_11828.warn);
                                        cache = (uu___159_11828.cache);
                                        nolabels = (uu___159_11828.nolabels);
                                        use_zfuel_name =
                                          (uu___159_11828.use_zfuel_name);
                                        encode_non_total_function_typ =
                                          (uu___159_11828.encode_non_total_function_typ)
                                      }  in
                                    let t_norm1 =
                                      FStar_Syntax_Subst.subst univ_subst
                                        t_norm
                                       in
                                    let e1 =
                                      let uu____11832 =
                                        FStar_Syntax_Subst.subst univ_subst e
                                         in
                                      FStar_Syntax_Subst.compress uu____11832
                                       in
                                    let uu____11833 =
                                      destruct_bound_function flid t_norm1 e1
                                       in
                                    (match uu____11833 with
                                     | ((binders,body,uu____11845,uu____11846),curry)
                                         ->
                                         ((let uu____11853 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding")
                                              in
                                           if uu____11853
                                           then
                                             let uu____11854 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders
                                                in
                                             let uu____11855 =
                                               FStar_Syntax_Print.term_to_string
                                                 body
                                                in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11854 uu____11855
                                           else ());
                                          (let uu____11857 =
                                             encode_binders None binders env'
                                              in
                                           match uu____11857 with
                                           | (vars,guards,env'1,binder_decls,uu____11873)
                                               ->
                                               let body1 =
                                                 let uu____11881 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1
                                                    in
                                                 if uu____11881
                                                 then
                                                   reify_body env'1.tcenv
                                                     body
                                                 else body  in
                                               let app =
                                                 mk_app1 curry f ftok vars
                                                  in
                                               let uu____11884 =
                                                 let uu____11889 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic)
                                                    in
                                                 if uu____11889
                                                 then
                                                   let uu____11895 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app
                                                      in
                                                   let uu____11896 =
                                                     encode_formula body1
                                                       env'1
                                                      in
                                                   (uu____11895, uu____11896)
                                                 else
                                                   (let uu____11902 =
                                                      encode_term body1 env'1
                                                       in
                                                    (app, uu____11902))
                                                  in
                                               (match uu____11884 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11916 =
                                                        let uu____11920 =
                                                          let uu____11921 =
                                                            let uu____11927 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2)
                                                               in
                                                            ([[app1]], vars,
                                                              uu____11927)
                                                             in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11921
                                                           in
                                                        let uu____11933 =
                                                          let uu____11935 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str
                                                             in
                                                          Some uu____11935
                                                           in
                                                        (uu____11920,
                                                          uu____11933,
                                                          (Prims.strcat
                                                             "equation_" f))
                                                         in
                                                      FStar_SMTEncoding_Term.Assume
                                                        uu____11916
                                                       in
                                                    let uu____11937 =
                                                      let uu____11939 =
                                                        let uu____11941 =
                                                          let uu____11943 =
                                                            let uu____11945 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1
                                                               in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11945
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11943
                                                           in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11941
                                                         in
                                                      FStar_List.append
                                                        decls1 uu____11939
                                                       in
                                                    (uu____11937, env1))))))
                           | uu____11948 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11967 = varops.fresh "fuel"  in
                             (uu____11967, FStar_SMTEncoding_Term.Fuel_sort)
                              in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel
                              in
                           let env0 = env1  in
                           let uu____11970 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12009  ->
                                     fun uu____12010  ->
                                       match (uu____12009, uu____12010) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let g =
                                             let uu____12092 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented"
                                                in
                                             varops.new_fvar uu____12092  in
                                           let gtok =
                                             let uu____12094 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token"
                                                in
                                             varops.new_fvar uu____12094  in
                                           let env3 =
                                             let uu____12096 =
                                               let uu____12098 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm])
                                                  in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12098
                                                in
                                             push_free_var env2 flid gtok
                                               uu____12096
                                              in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1))
                              in
                           match uu____11970 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks  in
                               let encode_one_binding env01 uu____12182
                                 t_norm uu____12184 =
                                 match (uu____12182, uu____12184) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12209;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12210;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12227 =
                                       FStar_Syntax_Subst.univ_var_opening
                                         uvs
                                        in
                                     (match uu____12227 with
                                      | (univ_subst,univ_vars1) ->
                                          let env' =
                                            let uu___160_12244 = env2  in
                                            let uu____12245 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env2.tcenv univ_vars1
                                               in
                                            {
                                              bindings =
                                                (uu___160_12244.bindings);
                                              depth = (uu___160_12244.depth);
                                              tcenv = uu____12245;
                                              warn = (uu___160_12244.warn);
                                              cache = (uu___160_12244.cache);
                                              nolabels =
                                                (uu___160_12244.nolabels);
                                              use_zfuel_name =
                                                (uu___160_12244.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___160_12244.encode_non_total_function_typ)
                                            }  in
                                          let t_norm1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst t_norm
                                             in
                                          let e1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst e
                                             in
                                          ((let uu____12249 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding")
                                               in
                                            if uu____12249
                                            then
                                              let uu____12250 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn
                                                 in
                                              let uu____12251 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1
                                                 in
                                              let uu____12252 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1
                                                 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12250 uu____12251
                                                uu____12252
                                            else ());
                                           (let uu____12254 =
                                              destruct_bound_function flid
                                                t_norm1 e1
                                               in
                                            match uu____12254 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12276 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding")
                                                     in
                                                  if uu____12276
                                                  then
                                                    let uu____12277 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders
                                                       in
                                                    let uu____12278 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body
                                                       in
                                                    let uu____12279 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals
                                                       in
                                                    let uu____12280 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres
                                                       in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12277 uu____12278
                                                      uu____12279 uu____12280
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12284 =
                                                    encode_binders None
                                                      binders env'
                                                     in
                                                  match uu____12284 with
                                                  | (vars,guards,env'1,binder_decls,uu____12302)
                                                      ->
                                                      let decl_g =
                                                        let uu____12310 =
                                                          let uu____12316 =
                                                            let uu____12318 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars
                                                               in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12318
                                                             in
                                                          (g, uu____12316,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name"))
                                                           in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12310
                                                         in
                                                      let env02 =
                                                        push_zfuel_name env01
                                                          flid g
                                                         in
                                                      let decl_g_tok =
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          (gtok, [],
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Token for fuel-instrumented partial applications"))
                                                         in
                                                      let vars_tm =
                                                        FStar_List.map
                                                          FStar_SMTEncoding_Util.mkFreeV
                                                          vars
                                                         in
                                                      let app =
                                                        let uu____12333 =
                                                          let uu____12337 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          (f, uu____12337)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12333
                                                         in
                                                      let gsapp =
                                                        let uu____12343 =
                                                          let uu____12347 =
                                                            let uu____12349 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm])
                                                               in
                                                            uu____12349 ::
                                                              vars_tm
                                                             in
                                                          (g, uu____12347)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12343
                                                         in
                                                      let gmax =
                                                        let uu____12353 =
                                                          let uu____12357 =
                                                            let uu____12359 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  [])
                                                               in
                                                            uu____12359 ::
                                                              vars_tm
                                                             in
                                                          (g, uu____12357)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12353
                                                         in
                                                      let body1 =
                                                        let uu____12363 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1
                                                           in
                                                        if uu____12363
                                                        then
                                                          reify_body
                                                            env'1.tcenv body
                                                        else body  in
                                                      let uu____12365 =
                                                        encode_term body1
                                                          env'1
                                                         in
                                                      (match uu____12365 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12376
                                                               =
                                                               let uu____12380
                                                                 =
                                                                 let uu____12381
                                                                   =
                                                                   let uu____12389
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                   ([[gsapp]],
                                                                    (Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12389)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12381
                                                                  in
                                                               let uu____12400
                                                                 =
                                                                 let uu____12402
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str
                                                                    in
                                                                 Some
                                                                   uu____12402
                                                                  in
                                                               (uu____12380,
                                                                 uu____12400,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12376
                                                              in
                                                           let eqn_f =
                                                             let uu____12405
                                                               =
                                                               let uu____12409
                                                                 =
                                                                 let uu____12410
                                                                   =
                                                                   let uu____12416
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12416)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12410
                                                                  in
                                                               (uu____12409,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12405
                                                              in
                                                           let eqn_g' =
                                                             let uu____12424
                                                               =
                                                               let uu____12428
                                                                 =
                                                                 let uu____12429
                                                                   =
                                                                   let uu____12435
                                                                    =
                                                                    let uu____12436
                                                                    =
                                                                    let uu____12439
                                                                    =
                                                                    let uu____12440
                                                                    =
                                                                    let uu____12444
                                                                    =
                                                                    let uu____12446
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____12446
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____12444)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12440
                                                                     in
                                                                    (gsapp,
                                                                    uu____12439)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12436
                                                                     in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12435)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12429
                                                                  in
                                                               (uu____12428,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12424
                                                              in
                                                           let uu____12458 =
                                                             let uu____12463
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02
                                                                in
                                                             match uu____12463
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12480)
                                                                 ->
                                                                 let vars_tm1
                                                                   =
                                                                   FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars1
                                                                    in
                                                                 let gapp =
                                                                   FStar_SMTEncoding_Util.mkApp
                                                                    (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1))
                                                                    in
                                                                 let tok_corr
                                                                   =
                                                                   let tok_app
                                                                    =
                                                                    let uu____12495
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    mk_Apply
                                                                    uu____12495
                                                                    (fuel ::
                                                                    vars1)
                                                                     in
                                                                   let uu____12498
                                                                    =
                                                                    let uu____12502
                                                                    =
                                                                    let uu____12503
                                                                    =
                                                                    let uu____12509
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12509)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12503
                                                                     in
                                                                    (uu____12502,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                   FStar_SMTEncoding_Term.Assume
                                                                    uu____12498
                                                                    in
                                                                 let uu____12520
                                                                   =
                                                                   let uu____12524
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp
                                                                     in
                                                                   match uu____12524
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12532
                                                                    =
                                                                    let uu____12534
                                                                    =
                                                                    let uu____12535
                                                                    =
                                                                    let uu____12539
                                                                    =
                                                                    let uu____12540
                                                                    =
                                                                    let uu____12546
                                                                    =
                                                                    let uu____12547
                                                                    =
                                                                    let uu____12550
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____12550,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12547
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12546)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12540
                                                                     in
                                                                    (uu____12539,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12535
                                                                     in
                                                                    [uu____12534]
                                                                     in
                                                                    (d3,
                                                                    uu____12532)
                                                                    in
                                                                 (match uu____12520
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr])))
                                                              in
                                                           (match uu____12458
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
                                                                  env02))))))))
                                  in
                               let uu____12585 =
                                 let uu____12592 =
                                   FStar_List.zip3 gtoks1 typs1 bindings  in
                                 FStar_List.fold_left
                                   (fun uu____12624  ->
                                      fun uu____12625  ->
                                        match (uu____12624, uu____12625) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12701 =
                                              encode_one_binding env01 gtok
                                                ty lb
                                               in
                                            (match uu____12701 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12592
                                  in
                               (match uu____12585 with
                                | (decls2,eqns,env01) ->
                                    let uu____12741 =
                                      let isDeclFun uu___126_12749 =
                                        match uu___126_12749 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12750 -> true
                                        | uu____12756 -> false  in
                                      let uu____12757 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten
                                         in
                                      FStar_All.pipe_right uu____12757
                                        (FStar_List.partition isDeclFun)
                                       in
                                    (match uu____12741 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns  in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12784 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12784
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg)
                    in
                 ([decl], env))
  
let rec encode_sigelt :
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun se  ->
      (let uu____12817 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12817
       then
         let uu____12818 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
           uu____12818
       else ());
      (let nm =
         let uu____12821 = FStar_Syntax_Util.lid_of_sigelt se  in
         match uu____12821 with | None  -> "" | Some l -> l.FStar_Ident.str
          in
       let uu____12824 = encode_sigelt' env se  in
       match uu____12824 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12833 =
                  let uu____12835 =
                    let uu____12836 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12836  in
                  [uu____12835]  in
                (uu____12833, e)
            | uu____12838 ->
                let uu____12839 =
                  let uu____12841 =
                    let uu____12843 =
                      let uu____12844 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12844  in
                    uu____12843 :: g  in
                  let uu____12845 =
                    let uu____12847 =
                      let uu____12848 =
                        FStar_Util.format1 "</end encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12848  in
                    [uu____12847]  in
                  FStar_List.append uu____12841 uu____12845  in
                (uu____12839, e)))

and encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12856 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12865 =
            let uu____12866 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____12866 Prims.op_Negation  in
          if uu____12865
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12886 ->
                   let uu____12887 =
                     let uu____12890 =
                       let uu____12891 =
                         let uu____12906 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL]))
                            in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12906)
                          in
                       FStar_Syntax_Syntax.Tm_abs uu____12891  in
                     FStar_Syntax_Syntax.mk uu____12890  in
                   uu____12887 None tm.FStar_Syntax_Syntax.pos
                in
             let encode_action env1 a =
               let uu____12959 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name
                  in
               match uu____12959 with
               | (aname,atok,env2) ->
                   let uu____12969 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ
                      in
                   (match uu____12969 with
                    | (formals,uu____12979) ->
                        let uu____12986 =
                          let uu____12989 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____12989 env2  in
                        (match uu____12986 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____12997 =
                                 let uu____12998 =
                                   let uu____13004 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13012  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____13004,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____12998
                                  in
                               [uu____12997;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))]
                                in
                             let uu____13019 =
                               let aux uu____13048 uu____13049 =
                                 match (uu____13048, uu____13049) with
                                 | ((bv,uu____13076),(env3,acc_sorts,acc)) ->
                                     let uu____13097 = gen_term_var env3 bv
                                        in
                                     (match uu____13097 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____13019 with
                              | (uu____13135,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____13149 =
                                      let uu____13153 =
                                        let uu____13154 =
                                          let uu____13160 =
                                            let uu____13161 =
                                              let uu____13164 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____13164)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13161
                                             in
                                          ([[app]], xs_sorts, uu____13160)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13154
                                         in
                                      (uu____13153, (Some "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____13149
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____13176 =
                                      let uu____13180 =
                                        let uu____13181 =
                                          let uu____13187 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____13187)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13181
                                         in
                                      (uu____13180,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____13176
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____13197 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____13197 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____13213,uu____13214,uu____13215) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13218 = new_term_constant_and_tok_from_lid env lid  in
          (match uu____13218 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13229,t,quals) ->
          let will_encode_definition =
            let uu____13235 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___127_13237  ->
                      match uu___127_13237 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13240 -> false))
               in
            Prims.op_Negation uu____13235  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____13246 = encode_top_level_val env fv t quals  in
             match uu____13246 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____13258 =
                   let uu____13260 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____13260  in
                 (uu____13258, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____13265) ->
          let uu____13268 = encode_formula f env  in
          (match uu____13268 with
           | (f1,decls) ->
               let g =
                 let uu____13277 =
                   let uu____13278 =
                     let uu____13282 =
                       let uu____13284 =
                         let uu____13285 = FStar_Syntax_Print.lid_to_string l
                            in
                         FStar_Util.format1 "Assumption: %s" uu____13285  in
                       Some uu____13284  in
                     let uu____13286 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str)
                        in
                     (f1, uu____13282, uu____13286)  in
                   FStar_SMTEncoding_Term.Assume uu____13278  in
                 [uu____13277]  in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13290,quals,uu____13292) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13300 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13307 =
                       let uu____13312 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____13312.FStar_Syntax_Syntax.fv_name  in
                     uu____13307.FStar_Syntax_Syntax.v  in
                   let uu____13316 =
                     let uu____13317 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____13317  in
                   if uu____13316
                   then
                     let val_decl =
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp), quals));
                         FStar_Syntax_Syntax.sigrng =
                           (se.FStar_Syntax_Syntax.sigrng)
                       }  in
                     let uu____13336 = encode_sigelt' env1 val_decl  in
                     match uu____13336 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs)
             in
          (match uu____13300 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13353,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13355;
                          FStar_Syntax_Syntax.lbtyp = uu____13356;
                          FStar_Syntax_Syntax.lbeff = uu____13357;
                          FStar_Syntax_Syntax.lbdef = uu____13358;_}::[]),uu____13359,uu____13360,uu____13361)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13377 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____13377 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let valid_b2t_x =
                 let uu____13395 =
                   let uu____13399 =
                     let uu____13401 =
                       FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])  in
                     [uu____13401]  in
                   ("Valid", uu____13399)  in
                 FStar_SMTEncoding_Util.mkApp uu____13395  in
               let decls =
                 let uu____13406 =
                   let uu____13408 =
                     let uu____13409 =
                       let uu____13413 =
                         let uu____13414 =
                           let uu____13420 =
                             let uu____13421 =
                               let uu____13424 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x])
                                  in
                               (valid_b2t_x, uu____13424)  in
                             FStar_SMTEncoding_Util.mkEq uu____13421  in
                           ([[valid_b2t_x]], [xx], uu____13420)  in
                         FStar_SMTEncoding_Util.mkForall uu____13414  in
                       (uu____13413, (Some "b2t def"), "b2t_def")  in
                     FStar_SMTEncoding_Term.Assume uu____13409  in
                   [uu____13408]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13406
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let
          (uu____13441,uu____13442,quals,uu____13444) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___128_13452  ->
                  match uu___128_13452 with
                  | FStar_Syntax_Syntax.Discriminator uu____13453 -> true
                  | uu____13454 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13456,lids,quals,uu____13459) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13468 =
                     let uu____13469 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____13469.FStar_Ident.idText  in
                   uu____13468 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___129_13471  ->
                     match uu___129_13471 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13472 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13475,quals,uu____13477) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___130_13489  ->
                  match uu___130_13489 with
                  | FStar_Syntax_Syntax.Projector uu____13490 -> true
                  | uu____13493 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____13500 = try_lookup_free_var env l  in
          (match uu____13500 with
           | Some uu____13504 -> ([], env)
           | None  ->
               let se1 =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp), quals));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13513,quals,uu____13515) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13529,uu____13530) ->
          let uu____13537 = encode_signature env ses  in
          (match uu____13537 with
           | (g,env1) ->
               let uu____13547 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___131_13557  ->
                         match uu___131_13557 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13558,Some "inversion axiom",uu____13559)
                             -> false
                         | uu____13561 -> true))
                  in
               (match uu____13547 with
                | (g',inversions) ->
                    let uu____13570 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___132_13580  ->
                              match uu___132_13580 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13581 ->
                                  true
                              | uu____13587 -> false))
                       in
                    (match uu____13570 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13598,tps,k,uu____13601,datas,quals) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___133_13612  ->
                    match uu___133_13612 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13613 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13620 = c  in
              match uu____13620 with
              | (name,args,uu____13624,uu____13625,uu____13626) ->
                  let uu____13629 =
                    let uu____13630 =
                      let uu____13636 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13643  ->
                                match uu____13643 with
                                | (uu____13647,sort,uu____13649) -> sort))
                         in
                      (name, uu____13636, FStar_SMTEncoding_Term.Term_sort,
                        None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13630  in
                  [uu____13629]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____13667 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13670 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____13670 FStar_Option.isNone))
               in
            if uu____13667
            then []
            else
              (let uu____13687 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____13687 with
               | (xxsym,xx) ->
                   let uu____13693 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13704  ->
                             fun l  ->
                               match uu____13704 with
                               | (out,decls) ->
                                   let uu____13716 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____13716 with
                                    | (uu____13722,data_t) ->
                                        let uu____13724 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____13724 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13753 =
                                                 let uu____13754 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____13754.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____13753 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13762,indices) ->
                                                   indices
                                               | uu____13778 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13790  ->
                                                         match uu____13790
                                                         with
                                                         | (x,uu____13794) ->
                                                             let uu____13795
                                                               =
                                                               let uu____13796
                                                                 =
                                                                 let uu____13800
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____13800,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13796
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____13795)
                                                    env)
                                                in
                                             let uu____13802 =
                                               encode_args indices env1  in
                                             (match uu____13802 with
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
                                                      let uu____13822 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13830
                                                                 =
                                                                 let uu____13833
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____13833,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13830)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____13822
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____13835 =
                                                      let uu____13836 =
                                                        let uu____13839 =
                                                          let uu____13840 =
                                                            let uu____13843 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____13843,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13840
                                                           in
                                                        (out, uu____13839)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13836
                                                       in
                                                    (uu____13835,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____13693 with
                    | (data_ax,decls) ->
                        let uu____13851 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____13851 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13862 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13862 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____13865 =
                                 let uu____13869 =
                                   let uu____13870 =
                                     let uu____13876 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____13884 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____13876,
                                       uu____13884)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13870
                                    in
                                 let uu____13892 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____13869, (Some "inversion axiom"),
                                   uu____13892)
                                  in
                               FStar_SMTEncoding_Term.Assume uu____13865  in
                             let pattern_guarded_inversion =
                               let uu____13896 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1"))
                                  in
                               if uu____13896
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                    in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp])
                                    in
                                 let uu____13904 =
                                   let uu____13905 =
                                     let uu____13909 =
                                       let uu____13910 =
                                         let uu____13916 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars)
                                            in
                                         let uu____13924 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax)
                                            in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13916, uu____13924)
                                          in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13910
                                        in
                                     let uu____13932 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str)
                                        in
                                     (uu____13909, (Some "inversion axiom"),
                                       uu____13932)
                                      in
                                   FStar_SMTEncoding_Term.Assume uu____13905
                                    in
                                 [uu____13904]
                               else []  in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion))))
             in
          let uu____13935 =
            let uu____13943 =
              let uu____13944 = FStar_Syntax_Subst.compress k  in
              uu____13944.FStar_Syntax_Syntax.n  in
            match uu____13943 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13973 -> (tps, k)  in
          (match uu____13935 with
           | (formals,res) ->
               let uu____13988 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____13988 with
                | (formals1,res1) ->
                    let uu____13995 = encode_binders None formals1 env  in
                    (match uu____13995 with
                     | (vars,guards,env',binder_decls,uu____14010) ->
                         let uu____14017 =
                           new_term_constant_and_tok_from_lid env t  in
                         (match uu____14017 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____14030 =
                                  let uu____14034 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____14034)  in
                                FStar_SMTEncoding_Util.mkApp uu____14030  in
                              let uu____14039 =
                                let tname_decl =
                                  let uu____14045 =
                                    let uu____14046 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14061  ->
                                              match uu____14061 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____14069 = varops.next_id ()  in
                                    (tname, uu____14046,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14069, false)
                                     in
                                  constructor_or_logic_type_decl uu____14045
                                   in
                                let uu____14074 =
                                  match vars with
                                  | [] ->
                                      let uu____14081 =
                                        let uu____14082 =
                                          let uu____14084 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14084
                                           in
                                        push_free_var env1 t tname
                                          uu____14082
                                         in
                                      ([], uu____14081)
                                  | uu____14088 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____14094 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14094
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____14103 =
                                          let uu____14107 =
                                            let uu____14108 =
                                              let uu____14116 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats, None, vars, uu____14116)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14108
                                             in
                                          (uu____14107,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____14103
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____14074 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____14039 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14139 =
                                       encode_term_pred None res1 env' tapp
                                        in
                                     match uu____14139 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14153 =
                                               let uu____14154 =
                                                 let uu____14158 =
                                                   let uu____14159 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14159
                                                    in
                                                 (uu____14158,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14154
                                                in
                                             [uu____14153]
                                           else []  in
                                         let uu____14162 =
                                           let uu____14164 =
                                             let uu____14166 =
                                               let uu____14167 =
                                                 let uu____14171 =
                                                   let uu____14172 =
                                                     let uu____14178 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____14178)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14172
                                                    in
                                                 (uu____14171, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14167
                                                in
                                             [uu____14166]  in
                                           FStar_List.append karr uu____14164
                                            in
                                         FStar_List.append decls1 uu____14162
                                      in
                                   let aux =
                                     let uu____14187 =
                                       let uu____14189 =
                                         inversion_axioms tapp vars  in
                                       let uu____14191 =
                                         let uu____14193 =
                                           pretype_axiom tapp vars  in
                                         [uu____14193]  in
                                       FStar_List.append uu____14189
                                         uu____14191
                                        in
                                     FStar_List.append kindingAx uu____14187
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14198,uu____14199,uu____14200,uu____14201,uu____14202,uu____14203)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14210,t,uu____14212,n_tps,quals,uu____14215) ->
          let uu____14220 = new_term_constant_and_tok_from_lid env d  in
          (match uu____14220 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])  in
               let uu____14231 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____14231 with
                | (formals,t_res) ->
                    let uu____14253 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____14253 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____14262 =
                           encode_binders (Some fuel_tm) formals env1  in
                         (match uu____14262 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____14300 =
                                            mk_term_projector_name d x  in
                                          (uu____14300,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____14302 =
                                  let uu____14312 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14312, true)
                                   in
                                FStar_All.pipe_right uu____14302
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                 in
                              let app = mk_Apply ddtok_tm vars  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let xvars =
                                FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                                  vars
                                 in
                              let dapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (ddconstrsym, xvars)
                                 in
                              let uu____14334 =
                                encode_term_pred None t env1 ddtok_tm  in
                              (match uu____14334 with
                               | (tok_typing,decls3) ->
                                   let uu____14341 =
                                     encode_binders (Some fuel_tm) formals
                                       env1
                                      in
                                   (match uu____14341 with
                                    | (vars',guards',env'',decls_formals,uu____14356)
                                        ->
                                        let uu____14363 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars'
                                             in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1)
                                             in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1
                                           in
                                        (match uu____14363 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14382 ->
                                                   let uu____14386 =
                                                     let uu____14387 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14387
                                                      in
                                                   [uu____14386]
                                                in
                                             let encode_elim uu____14394 =
                                               let uu____14395 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____14395 with
                                               | (head1,args) ->
                                                   let uu____14424 =
                                                     let uu____14425 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____14425.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____14424 with
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
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        let uu____14443 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____14443
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
                                                                 | uu____14469
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable"
                                                                  in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14477
                                                                    =
                                                                    let uu____14478
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14478
                                                                     in
                                                                    if
                                                                    uu____14477
                                                                    then
                                                                    let uu____14485
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14485]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____14487
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14500
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14500
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14522
                                                                    =
                                                                    let uu____14526
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14526
                                                                     in
                                                                    (match uu____14522
                                                                    with
                                                                    | 
                                                                    (uu____14533,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14539
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv
                                                                     in
                                                                    uu____14539
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14541
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14541
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int "0"))
                                                                 encoded_args
                                                                in
                                                             (match uu____14487
                                                              with
                                                              | (uu____14549,arg_vars,elim_eqns_or_guards,uu____14552)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1)
                                                                     in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1)
                                                                     in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty
                                                                     in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1
                                                                     in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____14571
                                                                    =
                                                                    let uu____14575
                                                                    =
                                                                    let uu____14576
                                                                    =
                                                                    let uu____14582
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14588
                                                                    =
                                                                    let uu____14589
                                                                    =
                                                                    let uu____14592
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14592)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14589
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14582,
                                                                    uu____14588)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14576
                                                                     in
                                                                    (uu____14575,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14571
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14605
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____14605,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14607
                                                                    =
                                                                    let uu____14611
                                                                    =
                                                                    let uu____14612
                                                                    =
                                                                    let uu____14618
                                                                    =
                                                                    let uu____14621
                                                                    =
                                                                    let uu____14623
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14623]
                                                                     in
                                                                    [uu____14621]
                                                                     in
                                                                    let uu____14626
                                                                    =
                                                                    let uu____14627
                                                                    =
                                                                    let uu____14630
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14631
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14630,
                                                                    uu____14631)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14627
                                                                     in
                                                                    (uu____14618,
                                                                    [x],
                                                                    uu____14626)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14612
                                                                     in
                                                                    let uu____14641
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14611,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14641)
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14607
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14646
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
                                                                    (let uu____14661
                                                                    =
                                                                    let uu____14662
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14662
                                                                    dapp1  in
                                                                    [uu____14661])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14646
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14666
                                                                    =
                                                                    let uu____14670
                                                                    =
                                                                    let uu____14671
                                                                    =
                                                                    let uu____14677
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14683
                                                                    =
                                                                    let uu____14684
                                                                    =
                                                                    let uu____14687
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14687)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14684
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14677,
                                                                    uu____14683)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14671
                                                                     in
                                                                    (uu____14670,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14666)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14697 ->
                                                        ((let uu____14699 =
                                                            let uu____14700 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d
                                                               in
                                                            let uu____14701 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1
                                                               in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14700
                                                              uu____14701
                                                             in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14699);
                                                         ([], [])))
                                                in
                                             let uu____14704 = encode_elim ()
                                                in
                                             (match uu____14704 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14716 =
                                                      let uu____14718 =
                                                        let uu____14720 =
                                                          let uu____14722 =
                                                            let uu____14724 =
                                                              let uu____14725
                                                                =
                                                                let uu____14731
                                                                  =
                                                                  let uu____14733
                                                                    =
                                                                    let uu____14734
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14734
                                                                     in
                                                                  Some
                                                                    uu____14733
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14731)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14725
                                                               in
                                                            [uu____14724]  in
                                                          let uu____14737 =
                                                            let uu____14739 =
                                                              let uu____14741
                                                                =
                                                                let uu____14743
                                                                  =
                                                                  let uu____14745
                                                                    =
                                                                    let uu____14747
                                                                    =
                                                                    let uu____14749
                                                                    =
                                                                    let uu____14750
                                                                    =
                                                                    let uu____14754
                                                                    =
                                                                    let uu____14755
                                                                    =
                                                                    let uu____14761
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14761)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14755
                                                                     in
                                                                    (uu____14754,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14750
                                                                     in
                                                                    let uu____14768
                                                                    =
                                                                    let uu____14770
                                                                    =
                                                                    let uu____14771
                                                                    =
                                                                    let uu____14775
                                                                    =
                                                                    let uu____14776
                                                                    =
                                                                    let uu____14782
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____14788
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14782,
                                                                    uu____14788)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14776
                                                                     in
                                                                    (uu____14775,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14771
                                                                     in
                                                                    [uu____14770]
                                                                     in
                                                                    uu____14749
                                                                    ::
                                                                    uu____14768
                                                                     in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14747
                                                                     in
                                                                  FStar_List.append
                                                                    uu____14745
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14743
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14741
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14739
                                                             in
                                                          FStar_List.append
                                                            uu____14722
                                                            uu____14737
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____14720
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____14718
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14716
                                                     in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))

and encode_signature :
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____14809  ->
              fun se  ->
                match uu____14809 with
                | (g,env1) ->
                    let uu____14821 = encode_sigelt env1 se  in
                    (match uu____14821 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14857 =
        match uu____14857 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14875 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort
                    in
                 ((let uu____14880 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____14880
                   then
                     let uu____14881 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____14882 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____14883 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14881 uu____14882 uu____14883
                   else ());
                  (let uu____14885 = encode_term t1 env1  in
                   match uu____14885 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____14895 =
                         let uu____14899 =
                           let uu____14900 =
                             let uu____14901 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____14901
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____14900  in
                         new_term_constant_from_string env1 x uu____14899  in
                       (match uu____14895 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t
                               in
                            let caption =
                              let uu____14912 = FStar_Options.log_queries ()
                                 in
                              if uu____14912
                              then
                                let uu____14914 =
                                  let uu____14915 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____14916 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____14917 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14915 uu____14916 uu____14917
                                   in
                                Some uu____14914
                              else None  in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym  in
                              FStar_SMTEncoding_Term.Assume
                                (t2, (Some a_name), a_name)
                               in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax])
                               in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14928,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None
                    in
                 let uu____14937 = encode_free_var env1 fv t t_norm []  in
                 (match uu____14937 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____14956 = encode_sigelt env1 se  in
                 (match uu____14956 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____14966 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____14966 with | (uu____14978,decls,env1) -> (decls, env1)
  
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15023  ->
            match uu____15023 with
            | (l,uu____15030,uu____15031) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None)))
     in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15052  ->
            match uu____15052 with
            | (l,uu____15060,uu____15061) ->
                let uu____15066 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l)
                   in
                let uu____15067 =
                  let uu____15069 =
                    let uu____15070 = FStar_SMTEncoding_Util.mkFreeV l  in
                    FStar_SMTEncoding_Term.Eval uu____15070  in
                  [uu____15069]  in
                uu____15066 :: uu____15067))
     in
  (prefix1, suffix) 
let last_env : env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let init_env : FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15081 =
      let uu____15083 =
        let uu____15084 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15084;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true
        }  in
      [uu____15083]  in
    FStar_ST.write last_env uu____15081
  
let get_env : FStar_TypeChecker_Env.env -> env_t =
  fun tcenv  ->
    let uu____15102 = FStar_ST.read last_env  in
    match uu____15102 with
    | [] -> failwith "No env; call init first!"
    | e::uu____15108 ->
        let uu___161_15110 = e  in
        {
          bindings = (uu___161_15110.bindings);
          depth = (uu___161_15110.depth);
          tcenv;
          warn = (uu___161_15110.warn);
          cache = (uu___161_15110.cache);
          nolabels = (uu___161_15110.nolabels);
          use_zfuel_name = (uu___161_15110.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___161_15110.encode_non_total_function_typ)
        }
  
let set_env : env_t -> Prims.unit =
  fun env  ->
    let uu____15114 = FStar_ST.read last_env  in
    match uu____15114 with
    | [] -> failwith "Empty env stack"
    | uu____15119::tl1 -> FStar_ST.write last_env (env :: tl1)
  
let push_env : Prims.unit -> Prims.unit =
  fun uu____15127  ->
    let uu____15128 = FStar_ST.read last_env  in
    match uu____15128 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___162_15149 = hd1  in
          {
            bindings = (uu___162_15149.bindings);
            depth = (uu___162_15149.depth);
            tcenv = (uu___162_15149.tcenv);
            warn = (uu___162_15149.warn);
            cache = refs;
            nolabels = (uu___162_15149.nolabels);
            use_zfuel_name = (uu___162_15149.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_15149.encode_non_total_function_typ)
          }  in
        FStar_ST.write last_env (top :: hd1 :: tl1)
  
let pop_env : Prims.unit -> Prims.unit =
  fun uu____15155  ->
    let uu____15156 = FStar_ST.read last_env  in
    match uu____15156 with
    | [] -> failwith "Popping an empty stack"
    | uu____15161::tl1 -> FStar_ST.write last_env tl1
  
let mark_env : Prims.unit -> Prims.unit = fun uu____15169  -> push_env () 
let reset_mark_env : Prims.unit -> Prims.unit =
  fun uu____15172  -> pop_env () 
let commit_mark_env : Prims.unit -> Prims.unit =
  fun uu____15175  ->
    let uu____15176 = FStar_ST.read last_env  in
    match uu____15176 with
    | hd1::uu____15182::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15188 -> failwith "Impossible"
  
let init : FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
  
let push : Prims.string -> Prims.unit =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg 
let pop : Prims.string -> Prims.unit =
  fun msg  -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg 
let mark : Prims.string -> Prims.unit =
  fun msg  -> mark_env (); varops.mark (); FStar_SMTEncoding_Z3.mark msg 
let reset_mark : Prims.string -> Prims.unit =
  fun msg  ->
    reset_mark_env ();
    varops.reset_mark ();
    FStar_SMTEncoding_Z3.reset_mark msg
  
let commit_mark : Prims.string -> Prims.unit =
  fun msg  ->
    commit_mark_env ();
    varops.commit_mark ();
    FStar_SMTEncoding_Z3.commit_mark msg
  
let encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____15233 = FStar_Options.log_queries ()  in
        if uu____15233
        then
          let uu____15235 =
            let uu____15236 =
              let uu____15237 =
                let uu____15238 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____15238 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____15237  in
            FStar_SMTEncoding_Term.Caption uu____15236  in
          uu____15235 :: decls
        else decls  in
      let env = get_env tcenv  in
      let uu____15245 = encode_sigelt env se  in
      match uu____15245 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15251 = caption decls  in
            FStar_SMTEncoding_Z3.giveZ3 uu____15251))
  
let encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      (let uu____15262 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____15262
       then
         let uu____15263 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15263
       else ());
      (let env = get_env tcenv  in
       let uu____15268 =
         encode_signature
           (let uu___163_15272 = env  in
            {
              bindings = (uu___163_15272.bindings);
              depth = (uu___163_15272.depth);
              tcenv = (uu___163_15272.tcenv);
              warn = false;
              cache = (uu___163_15272.cache);
              nolabels = (uu___163_15272.nolabels);
              use_zfuel_name = (uu___163_15272.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___163_15272.encode_non_total_function_typ)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____15268 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15284 = FStar_Options.log_queries ()  in
             if uu____15284
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___164_15289 = env1  in
               {
                 bindings = (uu___164_15289.bindings);
                 depth = (uu___164_15289.depth);
                 tcenv = (uu___164_15289.tcenv);
                 warn = true;
                 cache = (uu___164_15289.cache);
                 nolabels = (uu___164_15289.nolabels);
                 use_zfuel_name = (uu___164_15289.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___164_15289.encode_non_total_function_typ)
               });
            (let uu____15291 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____15291
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 decls1)))
  
let encode_query :
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_ErrorReporting.label Prims.list *
          FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl
          Prims.list)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____15326 =
           let uu____15327 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____15327.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15326);
        (let env = get_env tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____15335 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15356 = aux rest  in
                 (match uu____15356 with
                  | (out,rest1) ->
                      let t =
                        let uu____15374 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____15374 with
                        | Some uu____15378 ->
                            let uu____15379 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit
                               in
                            FStar_Syntax_Util.refine uu____15379
                              x.FStar_Syntax_Syntax.sort
                        | uu____15380 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____15383 =
                        let uu____15385 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___165_15386 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___165_15386.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___165_15386.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____15385 :: out  in
                      (uu____15383, rest1))
             | uu____15389 -> ([], bindings1)  in
           let uu____15393 = aux bindings  in
           match uu____15393 with
           | (closing,bindings1) ->
               let uu____15407 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____15407, bindings1)
            in
         match uu____15335 with
         | (q1,bindings1) ->
             let uu____15420 =
               let uu____15423 =
                 FStar_List.filter
                   (fun uu___134_15425  ->
                      match uu___134_15425 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15426 ->
                          false
                      | uu____15430 -> true) bindings1
                  in
               encode_env_bindings env uu____15423  in
             (match uu____15420 with
              | (env_decls,env1) ->
                  ((let uu____15441 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery"))
                       in
                    if uu____15441
                    then
                      let uu____15442 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15442
                    else ());
                   (let uu____15444 = encode_formula q1 env1  in
                    match uu____15444 with
                    | (phi,qdecls) ->
                        let uu____15456 =
                          let uu____15459 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15459 phi
                           in
                        (match uu____15456 with
                         | (labels,phi1) ->
                             let uu____15469 = encode_labels labels  in
                             (match uu____15469 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____15490 =
                                      let uu____15494 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____15495 =
                                        varops.mk_unique "@query"  in
                                      (uu____15494, (Some "query"),
                                        uu____15495)
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____15490
                                     in
                                  let suffix =
                                    let uu____15499 =
                                      let uu____15501 =
                                        let uu____15503 =
                                          FStar_Options.print_z3_statistics
                                            ()
                                           in
                                        if uu____15503
                                        then
                                          [FStar_SMTEncoding_Term.PrintStats]
                                        else []  in
                                      FStar_List.append uu____15501
                                        [FStar_SMTEncoding_Term.Echo "Done!"]
                                       in
                                    FStar_List.append label_suffix
                                      uu____15499
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  
let is_trivial :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env = get_env tcenv  in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15516 = encode_formula q env  in
       match uu____15516 with
       | (f,uu____15520) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15522) -> true
             | uu____15525 -> false)))
  